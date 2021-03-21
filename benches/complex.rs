use criterion::{criterion_group, criterion_main, Criterion};
use parsnip::{Arg, Args, NumValues, Results};
use std::convert::TryInto;

macro_rules! create_app {
    () => {{
        Args::<Results> {
            name: "parsnip tests",
            version: "0.1",
            about: "test parsnip lib",
            author: "Author <email@email.com>",
            args: vec![
                Arg {
                    name: "option",
                    short: Some("o"),
                    long: Some("option"),
                    about: "tests options",
                    num_values: NumValues::Fixed(1),
                    value_name: Some("opt"),
                    ..Default::default()
                },
                Arg {
                    name: "flag",
                    short: Some("f"),
                    long: Some("flag"),
                    about: "tests flags",
                    ..Default::default()
                },
                Arg {
                    // @todo: conflicts with flag, requires option2
                    name: "flag2",
                    short: Some("F"),
                    about: "tests flags",
                    ..Default::default()
                },
                Arg {
                    // @todo: conflicts with option, requires positional 2
                    name: "option2",
                    long: Some("long-option-2"),
                    about: "tests long options with exclusions",
                    num_values: NumValues::Fixed(1),
                    value_name: Some("option2"),
                    ..Default::default()
                },
                Arg {
                    name: "positional2",
                    about: "tests positionals with exclusions",
                    ..Default::default()
                },
                Arg {
                    // @todo: conflicts with option, requires positional 2
                    name: "option3",
                    short: Some("-O"),
                    long: Some("Option"),
                    about: "tests options with specific value sets",
                    num_values: NumValues::Fixed(1),
                    validation: |v| {
                        let s: &str = v.try_into().unwrap();
                        if (s == "fast" || s == "slow") {
                            Ok(())
                        } else {
                            Err("invalid".to_string())
                        }
                    },
                    value_name: Some("option2"),
                    ..Default::default()
                },
                Arg {
                    name: "positional3",
                    about: "tests positionals with specific values",
                    validation: |v| {
                        let s: &str = v.try_into().unwrap();
                        if (s == "vi" || s == "emacs") {
                            Ok(())
                        } else {
                            Err("invalid".to_string())
                        }
                    },
                    ..Default::default()
                },
                Arg {
                    name: "multvals",
                    long: Some("multvals"),
                    about: "Tests multiple values, not mult occs",
                    num_values: NumValues::Fixed(2),
                    ..Default::default()
                },
                Arg {
                    // @todo: not sure why this is considered different...
                    name: "multvalsmo",
                    long: Some("multvalsmo"),
                    about: "Tests multiple values, not mult occs",
                    num_values: NumValues::Fixed(2),
                    ..Default::default()
                },
                Arg {
                    name: "minvals2",
                    long: Some("minvals2"),
                    about: "Tests 2 min vals",
                    num_values: NumValues::AtLeast(2),
                    ..Default::default()
                },
                Arg {
                    name: "maxvals3",
                    long: Some("maxvals3"),
                    about: "Tests 3 max vals",
                    num_values: NumValues::Between(0, 3),
                    ..Default::default()
                },
            ],
            subcommands: vec![Args::<Results> {
                name: "subcmd",
                version: "0.1",
                about: "tests subcommands",
                author: "Author <email@email.com>",
                args: vec![Arg {
                    name: "option",
                    short: Some("o"),
                    long: Some("tests options"),
                    about: "Tests 3 max vals",
                    num_values: NumValues::Fixed(1),
                    value_name: Some("scoption"),
                    ..Default::default()
                }],
                ..Default::default()
            }],
            ..Default::default()
        }
    }};
}

pub fn build_from_usage(c: &mut Criterion) {
    c.bench_function("build_from_usage", |b| b.iter(|| create_app!()));
}

pub fn parse_complex(c: &mut Criterion) {
    c.bench_function("parse_complex", |b| b.iter(|| create_app!().parse(vec![""]).is_ok()));
}

pub fn parse_complex_with_flag(c: &mut Criterion) {
    c.bench_function("parse_complex_with_flag", |b| b.iter(|| create_app!().parse(vec!["myprog", "-f"]).is_ok()));
}

pub fn parse_complex_with_opt(c: &mut Criterion) {
    c.bench_function("parse_complex_with_opt", |b| {
        b.iter(|| create_app!().parse(vec!["myprog", "-o", "option1"]).is_ok())
    });
}

pub fn parse_complex_with_pos(c: &mut Criterion) {
    c.bench_function("parse_complex_with_pos", |b| b.iter(|| create_app!().parse(vec!["myprog", "arg1"]).is_ok()));
}

pub fn parse_complex_with_sc(c: &mut Criterion) {
    c.bench_function("parse_complex_with_sc", |b| b.iter(|| create_app!().parse(vec!["myprog", "subcmd"]).is_ok()));
}

pub fn parse_complex_with_sc_flag(c: &mut Criterion) {
    c.bench_function("parse_complex_with_sc_flag", |b| {
        b.iter(|| create_app!().parse(vec!["myprog", "subcmd", "-f"]).is_ok())
    });
}

pub fn parse_complex_with_sc_opt(c: &mut Criterion) {
    c.bench_function("parse_complex_with_sc_opt", |b| {
        b.iter(|| create_app!().parse(vec!["myprog", "subcmd", "-o", "option1"]).is_ok())
    });
}

pub fn parse_complex_with_sc_pos(c: &mut Criterion) {
    c.bench_function("parse_complex_with_sc_pos", |b| {
        b.iter(|| create_app!().parse(vec!["myprog", "subcmd", "arg1"]).is_ok())
    });
}

pub fn parse_complex1(c: &mut Criterion) {
    c.bench_function("parse_complex1", |b| {
        b.iter(|| {
            create_app!()
                .parse(vec![
                    "myprog",
                    "-ff",
                    "-o",
                    "option1",
                    "arg1",
                    "-O",
                    "fast",
                    "arg2",
                    "--multvals",
                    "one",
                    "two",
                    "emacs",
                ])
                .is_ok()
        })
    });
}

pub fn parse_complex2(c: &mut Criterion) {
    c.bench_function("parse_complex2", |b| {
        b.iter(|| {
            create_app!()
                .parse(vec![
                    "myprog",
                    "arg1",
                    "-f",
                    "arg2",
                    "--long-option-2",
                    "some",
                    "-O",
                    "slow",
                    "--multvalsmo",
                    "one",
                    "two",
                    "--minvals2",
                    "3",
                    "2",
                    "1",
                ])
                .is_ok()
        })
    });
}

pub fn parse_complex_with_sc_complex(c: &mut Criterion) {
    c.bench_function("parse_complex_with_sc_complex", |b| {
        b.iter(|| create_app!().parse(vec!["myprog", "subcmd", "-f", "-o", "option1", "arg1"]).is_ok())
    });
}

criterion_group!(
    benches,
    build_from_usage,
    parse_complex,
    parse_complex_with_flag,
    parse_complex_with_opt,
    parse_complex_with_pos,
    parse_complex_with_sc,
    parse_complex_with_sc_flag,
    parse_complex_with_sc_opt,
    parse_complex_with_sc_pos,
    parse_complex1,
    parse_complex2,
    parse_complex_with_sc_complex
);

criterion_main!(benches);
