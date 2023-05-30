use std::{marker::PhantomData, fs::File, io::{BufReader, BufWriter, Write}, time::Instant};
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::{Rotation, kzg::{commitment::{ParamsKZG, KZGCommitmentScheme}, multiopen::{ProverSHPLONK, VerifierSHPLONK}, strategy::SingleStrategy}}, SerdeFormat, transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer, Blake2bRead, TranscriptReadBuffer}};
use halo2_proofs::halo2curves::bn256::{Fr, Bn256, G1Affine};
use rand_core::OsRng;
#[cfg(feature = "dev-graph")]
use plotters::prelude::*;

const K: u32 = 16;

#[derive(Debug, Clone)]
struct AddAndXorConfig {
    pub advice: Column<Advice>,
    pub advice_xor: Column<Advice>,
    pub advice_sbox: Column<Advice>,
    pub s_add: Selector,
    pub xor_table: TableColumn,
    pub instance: Column<Instance>,
    pub xor_with: Column<Fixed>,
    pub xor_with_value: u64,
}

#[derive(Debug, Clone)]
struct AddAndXorChip<F: FieldExt> {
    config: AddAndXorConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AddAndXorChip<F> {
    pub fn construct(config: AddAndXorConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>, xor_with_value: u64) -> AddAndXorConfig {
        let col_a = meta.advice_column();
        let col_xor = meta.advice_column();
        let col_sbox = meta.advice_column();
        let s_add = meta.selector();
        let instance = meta.instance_column();
        let xor_with = meta.fixed_column();

        let xor_table = meta.lookup_table_column();

        meta.enable_equality(col_a);
        meta.enable_equality(col_xor);
        meta.enable_equality(col_sbox);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            let s = meta.query_selector(s_add);
            let a_prev = meta.query_advice(col_a, Rotation::prev());
            let a = meta.query_advice(col_a, Rotation::cur());
            let inc = meta.query_fixed(xor_with, Rotation::cur());

            vec![
                s * (a_prev + inc - a),
            ]
        });

        meta.create_gate("sbox", |meta| {
            let s = meta.query_selector(s_add);
            let a = meta.query_advice(col_xor, Rotation::cur());
            let sbox = meta.query_advice(col_sbox, Rotation::cur());

            vec![
                s * (a.clone() * a.clone() * a.clone() * a.clone() * a.clone() - sbox)
            ]
        });

        meta.lookup("xor lookup",|meta| {
            let value = meta.query_advice(col_xor, Rotation::cur());
            vec![
                (value, xor_table),
            ]
        });

        AddAndXorConfig {
            advice: col_a,
            advice_xor: col_xor,
            advice_sbox: col_sbox,
            s_add,
            xor_table,
            instance,
            xor_with,
            xor_with_value
        }
    }

    fn load_table(
        &self,
        mut layouter: impl Layouter<F>,
        xor_with: u64,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "xor table",
            |mut table| {
                for value in 0..(1<<(K - 1)) + 1 {
                    table.assign_cell(
                        || "value",
                        self.config.xor_table,
                        value,
                        || Value::known(F::from(value as u64 ^ xor_with)),
                    )?;
                }
                Ok(())
            }
        )
    }

    #[allow(clippy::type_complexity)]
    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        xor_with: u64,
        nrows: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "entire circuit",
            |mut region| {
                region.assign_fixed(
                    || "xor_with",
                    self.config.xor_with,
                    0,
                    || Value::known(F::from(xor_with)))?;

                // assign first row
                let mut a_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    0,
                    self.config.advice,
                    0,
                )?;

                let mut xor_cell = region.assign_advice(
                    || "xor",
                    self.config.advice_xor,
                    0,
                    || a_cell.value().copied(),
                )?;

                let mut sbox_cell = region.assign_advice(
                    || "sboc",
                    self.config.advice_sbox,
                    0,
                    || a_cell.value().copied(),
                )?;

                // assign the rest of rows
                for row in 1..nrows {
                    region.assign_fixed(
                        || "xor_with",
                        self.config.xor_with,
                        row,
                        || Value::known(F::from(xor_with))
                    )?;
                    self.config.s_add.enable(&mut region, row)?;

                    a_cell = region.assign_advice(
                        || "a_cell",
                        self.config.advice,
                        row,
                        || a_cell.value().copied().map(|a| { a + F::from(xor_with) })
                    )?;

                    xor_cell = region.assign_advice(
                        || "advice_xor",
                        self.config.advice_xor,
                        row,
                        || a_cell.value().map(|a| {
                            let a_val = a.get_lower_32() as u64;
                            F::from(a_val ^ xor_with)
                        }),
                    )?;

                    sbox_cell = region.assign_advice(
                        || "sbox_cell",
                        self.config.advice_sbox,
                        row,
                        || xor_cell.value().copied().map(|a| { a * a * a * a * a })
                    )?;
                    //println!("a_cell: {:?}, xor_cell: {:?}, sbox: {:?}", a_cell.value(), xor_cell.value(), sbox_cell.value());
                }
                Ok(xor_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F>(PhantomData<F>);

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = AddAndXorConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        AddAndXorChip::configure(meta, 1)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = AddAndXorChip::construct(config);
        chip.load_table(layouter.namespace(|| "lookup table"), chip.config.xor_with_value)?;
        let out_cell = chip.assign(
            layouter.namespace(|| "entire table"),
            chip.config.xor_with_value,
            1 << (K-1))?;
        chip.expose_public(layouter.namespace(|| "out"), out_cell, 1)?;

        Ok(())
    }
}

fn main() {
    let a = Fr::from(1); // F[0]
    let out = Fr::from((1 << (K - 1)) ^ 1); // F[1 << K]

    let circuit = MyCircuit(PhantomData);

    #[cfg(feature = "dev-graph")]
    {
        let dot_string = halo2_proofs::dev::circuit_dot_graph(&circuit);
        print!("{}", dot_string);

        let root = BitMapBackend::new("fib-4-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fib 2 Layout", ("sans-serif", 60)).unwrap();
        halo2_proofs::dev::CircuitLayout::default()
        .render(K, &circuit, &root)
        .unwrap();
    }

    let mut public_input = vec![a, out];

    let params = ParamsKZG::<Bn256>::setup(K, OsRng);

    let vk_name = format!("fib4-{}.vk", K);
    let pk_name = format!("fib4-{}.pk", K);
    std::fs::remove_file(pk_name.clone());
    std::fs::remove_file(vk_name.clone());

    let read_from_file = std::path::Path::new(&vk_name).exists() && std::path::Path::new(&pk_name).exists();

    let vk = if read_from_file {
        let f = File::open(vk_name).unwrap();
        let mut reader = BufReader::new(f);
        VerifyingKey::<G1Affine>::read::<_, MyCircuit<_>>(&mut reader, SerdeFormat::RawBytes)
            .unwrap()
    } else {
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        let f = File::create(vk_name).unwrap();
        let mut writer = BufWriter::new(f);
        vk.write(&mut writer, SerdeFormat::RawBytes).unwrap();
        writer.flush().unwrap();
        println!("VK generated");
        vk
    };

    let pk = if read_from_file {
        let f = File::open(pk_name).unwrap();
        let mut reader = BufReader::new(f);
        ProvingKey::<G1Affine>::read::<_, MyCircuit<_>>(&mut reader, SerdeFormat::RawBytes)
            .unwrap()
    } else {
        let pk = keygen_pk(&params, vk.clone(), &circuit).expect("keygen_pk should not fail");
        let f = File::create(pk_name).unwrap();
        let mut writer = BufWriter::new(f);
        pk.write(&mut writer, SerdeFormat::RawBytes).unwrap();
        writer.flush().unwrap();
        println!("PK generated");
        pk
    };

    println!("k = {}", &pk.get_vk().get_domain().k());
    println!("extended_k = {}", &pk.get_vk().get_domain().extended_k());

    let rng = OsRng;

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    let start = Instant::now();
    create_proof::<KZGCommitmentScheme<Bn256>, ProverSHPLONK<_, >, _, _, _, _>(
        &params,
        &pk,
        &[circuit],
        &[&[&public_input]],
        rng,
        &mut transcript,
    )
    .unwrap();

    let duration = start.elapsed();
    println!("Total time in create proof: {:?}", duration);
    let trs = transcript.finalize().to_vec();

    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(trs.as_slice());

    let strategy = SingleStrategy::new(&params);
    verify_proof::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<Bn256>, _, _, _>(&params, &vk, strategy, &[&[&public_input]], &mut transcript).unwrap();
}