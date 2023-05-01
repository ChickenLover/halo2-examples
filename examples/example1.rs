use std::{marker::PhantomData, fs::File, io::{BufWriter, BufReader, Write}};
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::{Rotation, kzg::{commitment::{ParamsKZG, KZGCommitmentScheme}, multiopen::{ProverGWC, ProverSHPLONK}}}, SerdeFormat};
use std::{time::Instant};

use halo2_proofs::{dev::MockProver, poly::{ipa::{commitment::{ParamsIPA, IPACommitmentScheme}, multiopen::ProverIPA}, commitment::ParamsProver}, plonk::{keygen_vk, keygen_pk, create_proof}, transcript::{Blake2bWrite, Challenge255, TranscriptWriterBuffer}};
use halo2curves::{pasta::{Fp, EqAffine}, bn256::{Bn256, G1Affine, Fr}};
use rand_core::OsRng;
use peak_alloc::PeakAlloc;

#[derive(Debug, Clone)]
struct FibonacciConfig {
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}

const K: u32 = 19;

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
        let col_c = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            vec![s * (a + b - c)]
        });

        FibonacciConfig {
            col_a,
            col_b,
            col_c,
            selector,
            instance,
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let a_cell = region.assign_advice_from_instance(
                    || "f(0)",
                    self.config.instance,
                    0,
                    self.config.col_a,
                    0)?;

                let b_cell = region.assign_advice_from_instance(
                    || "f(1)",
                    self.config.instance,
                    1,
                    self.config.col_b,
                    0)?;

                let c_cell = region.assign_advice(
                    || "a + b",
                    self.config.col_c,
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;

                Ok((a_cell, b_cell, c_cell))
            },
        )
    }

    pub fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        prev_b: &AssignedCell<F, F>,
        prev_c: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                // Copy the value from b & c in previous row to a & b in current row
                prev_b.copy_advice(
                    || "a",
                    &mut region,
                    self.config.col_a,
                    0,
                )?;
                prev_c.copy_advice(
                    || "b",
                    &mut region,
                    self.config.col_b,
                    0,
                )?;

                let c_cell = region.assign_advice(
                    || "c",
                    self.config.col_c,
                    0,
                    || prev_b.value().copied() + prev_c.value(),
                )?;

                Ok(c_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
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

        let (_, mut prev_b, mut prev_c) =
            chip.assign_first_row(layouter.namespace(|| "first row"))?;

        for _i in 3..(1 << K - 1) {
            let c_cell = chip.assign_row(layouter.namespace(|| "next row"), &prev_b, &prev_c)?;
            prev_b = prev_c;
            prev_c = c_cell;
        }

        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 2)?;

        Ok(())
    }
}

fn main() {
    let a = Fr::from(1); // F[0]
    let b = Fr::from(1); // F[1]
    let out = Fr::from(55); // F[9]

    let circuit = MyCircuit(PhantomData);

    let public_input = vec![a, b, out];

    // let params: ParamsIPA<EqAffine> = ParamsIPA::new(k);
    let params = ParamsKZG::<Bn256>::setup(K, OsRng);

    let vk_name = format!("fib-{}.vk", K);
    let pk_name = format!("fib-{}.pk", K);
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
    .expect("proof generation should not fail");

    let duration = start.elapsed();
    println!("Total time in create proof: {:?}", duration);
    transcript.finalize();
}

#[cfg(test)]
mod tests {

    #[test]

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_fibonacci1() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("fib-1-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Fib 1 Layout", ("sans-serif", 60)).unwrap();

        let circuit = MyCircuit::<Fp>(PhantomData);
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}
