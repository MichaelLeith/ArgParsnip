# Parsnip

A small Rust Argparser

# Setup
Add the lib to your `Cargo.toml`.

```
[dependencies]
parsnip = "0.1.0"
```

# Features

* **Autogenerated help/version commands**
  - can be overwritten
  - <program> [subcommand]* help & <program> [subcommand]* version commands are also generated
  - name/version/about parameters default to using Cargo.toml `CARGO_PKG_NAME/CARGO_PKG_VERSION/CARGO_PKG_DESCRIPTION` variables
* **Arguments**
  - supports short `-h` and `--help` syntax
  - unicode support by default
  - **Flags**
    - supports combinations (e.g `-rli` is the same as `-r -l -i`)
    - supports repeats, e.g `-vvv -v` will count as the same flag `v` appearing 4 times
  - **With Values**
    - supports constraints on the number of values for an arg, e.g having exactly one value, having between 2 & 4 values, having any number of values. E.g `-v foo bar`
    - supports restricting values to specific *primitive* types (any, bool, i32, i64, f32, f64, String) via the TryInto trait
    - supports additional custom validation (so you can e.g write your own sum type restrictions)
    - supports default values
  - **Combinations**
    - Parsing can be configured to fail if any required argument is missing
    - supports requiring at least one of a set of arguments (e.g A || B || C)
    - supports requiring all arguments in a set (e.g A && B && C)
    - supports inverting sets (e.g !(A && B))
    - supports requiring any or all of multiple sets (e.g (A && B) || (A && C)). This can also be negated
  - **Positional**
    - supports unix `--`, i.e `foo -- -a -b -c` will recieve positional arguments ["-a", "-b", "-c"]
    - treats all args that don't start with `-` or `--` as positional.
* **Subcommands**
  - e.g cargo run vs cargo test (run/test are subcommands)
  - subcommands can have their own subcommands and arguments
  - help/version commands are generated separately for each subcommand
* **Optional Callback support**
  - Instead of returning a results object with the argparsing results, A handler fn(Results) -> T can be provided for each command/subcommand (not supported when using serde).
* **no_std support**
  - disable default features to enable no_std
  - `parsnip = { version = "x", default-features = false }`
* **serde support**
  - `parsnip = { version = "x", features = ["derive"] }`
  - write your args schema in any format with a serde parser (serde_json, toml etc.), see derive-test for an example
* **Other opt-in features**
  - *debug* - enables logging info about arg parsing

# Usage

Here are some quick common cases. For more examples please look at the tests in `lib.rs`

## Examples

**Check if a flag was given once**

```
// ./prog --arg
fn main() {
    let args = Args {
        args: vec![Arg {
            name: "arg",
            short: Some("a"),
            about: "a flag",
            long: Some("arg"),
            required: true,
            ..Default::default()
        }],
        ..Default::default() 
    };
    let results = args.parse(std::env::args());
    assert_eq!(1, results.flags("arg"));
}
```

**Get the value of an arg**

```
// ./prog -a 1
fn main() {
    let args = Args {
        args: vec![Arg {
            name: "arg",
            short: Some("a"),
            default: Some(|| { Value::From(2) }),
            value_type: Type::Int,
            num_values: NumValues::Fixed(1),
            ..Default::default()
        }],
        ..Default::default()
    };
    let results = args.parse(std::env::args());
    assert_eq!(1, results.params.get("arg")?.try_into());
}
```

**Validate an argument**

```
// ./prog -a 1 2
fn main() {
    let args = Args {
        args: vec![Arg {
            name: "arg",
            short: Some("a"),
            value_type: Type::Int,
            num_values: NumValues::AtLeast(1),
            validation: |val| {
                let val: &i32 = v.try_into().unwrap();
                if 2 >= *val {
                    Ok(())
                } else {
                    Err("failed validation")
                }
            }
            ..Default::default()
        }],
        ..Default::default()
    };
    let results = args.parse(std::env::args());
    assert_eq!(vec![1, 2], results.params.get("arg")?.try_into());
}
```

**Using Subcommand**

```
// ./prog sub --arg 
fn main() {
    let args = Args {
        args: vec![Arg {
            name: "arg",
            long: Some("arg"),
            num_values: NumValues::None,
            ..Default::default()
        }],
        subcommands: vec![Args {
            name: "sub",
            path: Some("main/sub"),
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            ..Default::default()
        }],
        ..Default::default()
    };
    let results = args.parse(std::env::args());
    // this is the unique identifier for the subcommand
    assert_eq!("main/sub", results.path);
    assert_eq!(1, results.flags["arg"]);
}
```

## Documentation

# Development

## TODO

* Benchmarks
* More tests
* Features
** Support positional arguments
** Bash/Zsh completion
** Support disabling positional args
** Support updating repeats, e.g --arg Foo --arg Bar should give {"arg": ["Foo", "Bar"]} 
* Pretty sure my design isn't iterator friendly, try using a counter instead
