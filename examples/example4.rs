use std::{marker::PhantomData, fs::File, io::{BufReader, BufWriter, Write}, time::Instant};
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::{Rotation, kzg::{commitment::{ParamsKZG, KZGCommitmentScheme}, multiopen::ProverSHPLONK}}, SerdeFormat, transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer}};
use halo2curves::bn256::{Fr, Bn256, G1Affine};
use rand_core::OsRng;
#[cfg(feature = "dev-graph")]
use plotters::prelude::*;

const K: u32 = 16;

#[derive(Debug, Clone)]
struct FibonacciConfig {
    pub advice: [Column<Advice>; 3],
    pub s_add: Selector,
    pub s_reduction: Selector,
    pub reduction_table: [TableColumn; 3],
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct FibonacciChip<F: FieldExt> {
    config: FibonacciConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FibonacciChip<F> {
    pub fn construct(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> FibonacciConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let s_add = meta.selector();
        let s_reduction = meta.complex_selector();
        let instance = meta.instance_column();

        let reduction_table = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("fib mul", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            let s = meta.query_selector(s_add);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());

            vec![
                s * (a * b - c),
            ]
        });

        meta.lookup("lookup",|meta| {
            let s = meta.query_selector(s_reduction);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, reduction_table[0]),
                (s.clone() * rhs, reduction_table[1]),
                (s * out, reduction_table[2]),
            ]
        });

        FibonacciConfig {
            advice: [col_a, col_b, col_c],
            s_add,
            s_reduction,
            reduction_table,
            instance,
        }
    }

    fn load_table(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "reduction_table",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..512 {
                    for rhs in 0..512 {
                        table.assign_cell(
                            || "lhs",
                            self.config.reduction_table[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.reduction_table[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.reduction_table[2],
                            idx,
                            || Value::known(F::from((lhs * rhs) & u8::MAX as u64)),
                        )?;
                        idx += 1;
                    }
                }
                Ok(())
            }
        )
    }

    #[allow(clippy::type_complexity)]
    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        nrows: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "entire circuit",
            |mut region| {
                self.config.s_add.enable(&mut region, 0)?;

                // assign first row
                let a_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    0,
                    self.config.advice[0],
                    0,
                )?;
                let mut b_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    1,
                    self.config.advice[1],
                    0,
                )?;
                let mut c_cell = region.assign_advice(
                    || "add",
                    self.config.advice[2],
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;

                // assign the rest of rows
                for row in 1..nrows {
                    b_cell.copy_advice(
                        || "a",
                        &mut region,
                        self.config.advice[0],
                        row,
                    )?;
                    c_cell.copy_advice(
                        || "b",
                        &mut region,
                        self.config.advice[1],
                        row,
                    )?;

                    let new_c_cell = if row % 2 == 0 {
                        self.config.s_add.enable(&mut region, row)?;
                        region.assign_advice(
                            || "advice",
                            self.config.advice[2],
                            row,
                            || b_cell.value().copied() + c_cell.value(),
                        )?
                    } else {
                        self.config.s_reduction.enable(&mut region, row)?;
                        region.assign_advice(
                            || "advice",
                            self.config.advice[2],
                            row,
                            || b_cell.value().and_then(|a| c_cell.value().map(|b| {
                                let a_val = a.get_lower_32() as u64;
                                let b_val = b.get_lower_32() as u64;
                                F::from((a_val ^ b_val) & u8::MAX as u64)
                            })),
                        )?
                    };

                    b_cell = c_cell;
                    c_cell = new_c_cell;
                    println!("c_cell: {:?}", c_cell.value());
                }
                Ok(c_cell)
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
    type Config = FibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FibonacciChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FibonacciChip::construct(config);
        chip.load_table(layouter.namespace(|| "lookup table"))?;
        let out_cell = chip.assign(layouter.namespace(|| "entire table"), 1 << (K - 1))?;
        chip.expose_public(layouter.namespace(|| "out"), out_cell, 2)?;

        Ok(())
    }
}

fn main() {
    let a = Fr::from(1); // F[0]
    let b = Fr::from(1); // F[1]
    let out = Fr::from(0xb5); // F[1 << K]

    let circuit = MyCircuit(PhantomData);

    #[cfg(feature = "dev-graph")]
    {
        let root = BitMapBackend::new("fib-4-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fib 2 Layout", ("sans-serif", 60)).unwrap();
        halo2_proofs::dev::CircuitLayout::default()
        .render(1 << (K - 1), &circuit, &root)
        .unwrap();
    }

    let mut public_input = vec![a, b, out];

    let params = ParamsKZG::<Bn256>::setup(K, OsRng);

    let vk_name = format!("fib4-{}.vk", K);
    let pk_name = format!("fib4-{}.pk", K);
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
        let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
        let f = File::create(pk_name).unwrap();
        let mut writer = BufWriter::new(f);
        pk.write(&mut writer, SerdeFormat::RawBytes).unwrap();
        writer.flush().unwrap();
        println!("PK generated");
        pk
    };

    println!("k = {}", &pk.get_vk().get_domain().k());
    println!("extended_k = {}", &pk.get_vk().get_domain().extended_k());
    // std::fs::remove_file(pk_name).unwrap();

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
    transcript.finalize();
}