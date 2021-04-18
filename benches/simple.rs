use criterion::{criterion_group, criterion_main, Criterion};
use parsnip::{Arg, Args, NumValues, Results};

macro_rules! create_args {
    () => {{
        Args::<Results> {
            name: "parsnip tests",
            version: "0.1",
            about: "test parsnip lib",
            args: vec![
                Arg {
                    name: "flag",
                    short: Some("f"),
                    long: Some("flag"),
                    about: "tests flags",
                    ..Default::default()
                },
                Arg {
                    name: "option",
                    short: Some("o"),
                    long: Some("option"),
                    about: "tests options",
                    num_values: NumValues::Fixed(1),
                    value_name: Some("opt"),
                    ..Default::default()
                },
            ],
            ..Default::default()
        }
    }};
}

pub fn build_simple(c: &mut Criterion) {
    c.bench_function("build_simple", |b| b.iter(|| create_args!()));
}

pub fn build_with_flag(c: &mut Criterion) {
    c.bench_function("build_with_flag", |b| {
        b.iter(|| Args::<Results> {
            name: "parsnip test",
            args: vec![Arg {
                short: Some("s"),
                long: Some("some"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            ..Default::default()
        })
    });
}

pub fn build_with_opt(c: &mut Criterion) {
    c.bench_function("build_with_opt", |b| {
        b.iter(|| Args::<Results> {
            name: "parsnip test",
            args: vec![Arg {
                short: Some("s"),
                long: Some("some"),
                value_name: Some("FILE"),
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            ..Default::default()
        })
    });
}

pub fn parse_simple_with_flag(c: &mut Criterion) {
    c.bench_function("parse_simple_with_flag", |b| b.iter(|| create_args!().parse(vec!["myprog", "-f"]).is_ok()));
}

pub fn parse_simple_with_opt(c: &mut Criterion) {
    c.bench_function("parse_simple_with_opt", |b| {
        b.iter(|| create_args!().parse(vec!["myprog", "-o", "option1"]).is_ok())
    });
}

pub fn parse_simple_with_pos(c: &mut Criterion) {
    c.bench_function("parse_simple_with_pos", |b| b.iter(|| create_args!().parse(vec!["myprog", "arg1"]).is_ok()));
}

pub fn parse_simple_with_complex(c: &mut Criterion) {
    c.bench_function("parse_simple_with_complex", |b| {
        b.iter(|| create_args!().parse(vec!["myprog", "-o", "option1", "-f", "arg1"]).is_ok())
    });
}

criterion_group!(
    benches,
    parse_simple_with_complex,
    parse_simple_with_pos,
    parse_simple_with_opt,
    parse_simple_with_flag,
    build_with_opt,
    build_with_flag,
    build_simple
);

criterion_main!(benches);
