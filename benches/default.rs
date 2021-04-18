use argparsnip::{Args, Results};
use criterion::{criterion_group, criterion_main, Criterion};

pub fn build_empty(c: &mut Criterion) {
    c.bench_function("build_empty", |b| b.iter(|| Args::<Results>::default()));
}

pub fn parse_empty(c: &mut Criterion) {
    c.bench_function("parse_empty", |b| {
        b.iter(|| Args::<Results>::default().parse(Vec::<String>::with_capacity(0)).is_ok())
    });
}

criterion_group!(benches, build_empty, parse_empty);
criterion_main!(benches);
