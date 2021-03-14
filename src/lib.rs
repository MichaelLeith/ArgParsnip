#![cfg_attr(not(feature = "std"), no_std)]
extern crate alloc;

#[cfg(not(feature = "std"))]
mod std;

mod value;

use std::collections::HashMap;
use std::iter::Peekable;
use std::string::String;
use std::vec::Vec;

use crate::value::{cast_type, check_type, Type, Value};
use unicode_segmentation::UnicodeSegmentation;

use log::debug;

#[derive(Debug, PartialEq)]
pub enum Error<'a> {
    UnknownArg(String),
    InvalidArg,
    MissingRequiredArgs(Vec<&'a str>),
    // @todo: lets avoid exposing Value here
    WrongNumValues(&'a str, &'a NumValues, Value),
    WrongValueType(Value),
    WrongCastType(String),
    InvalidValue(String, String),
}

#[allow(dead_code)]
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum NumValues {
    None,
    Fixed(usize),
    AtLeast(usize),
    Between(usize, usize),
    Any,
}

impl Default for NumValues {
    fn default() -> Self {
        NumValues::Any
    }
}

#[derive(Debug, Default)]
pub struct Arg<'a> {
    // unique key to identify this arg
    pub name: &'a str,
    // aliases we'll match this arg with e.g -t --test
    pub short: Option<&'a str>,
    pub long: Option<&'a str>,
    // info about this arg
    pub about: &'a str,
    // number of parameters this arg accepts
    pub num_values: NumValues,
    // name for the value of this arg in --help
    pub value_name: Option<&'a str>,
    // default value for this arg
    pub default: Option<fn() -> Value>,
    // whether this arg is required
    pub required: bool,
    // type for values
    pub value_type: Type,
    // @todo: can we provide a default and avoid the Option?
    pub validation: Option<fn(Value) -> Result<Value, String>>,
}

#[derive(Debug)]
pub struct Args<'a, T> {
    pub name: &'a str,
    pub version: &'a str,
    pub author: &'a str,
    pub about: &'a str,
    pub args: Vec<Arg<'a>>,
    pub subcommands: Vec<Args<'a, T>>,
    // handler to invoke when this command has been found.
    // This is not called if a subcommand is invoked
    pub handler: fn(Results<'a>) -> T,
}

impl<'a, T: Default> Default for Args<'a, T> {
    fn default() -> Self {
        Args {
            name: Default::default(),
            version: Default::default(),
            author: Default::default(),
            about: Default::default(),
            args: Default::default(),
            subcommands: Default::default(),
            handler: |_| Default::default(),
        }
    }
}

#[derive(Debug)]
pub struct Results<'a> {
    pub params: HashMap<&'a str, Value>,
    pub unknown_params: Vec<String>,
    pub positional: Vec<String>,
}

impl<'a> Default for Results<'a> {
    fn default() -> Self {
        Results {
            params: Default::default(),
            unknown_params: Default::default(),
            positional: Default::default(),
        }
    }
}

impl<'a, R> Args<'a, R> {
    #[allow(dead_code)]
    pub fn parse_str<'b, T: IntoIterator<Item = &'b str>>(&'a self, args: T) -> Result<R, Error> {
        self.parse(args.into_iter().map(|a| String::from(a)))
    }

    #[allow(dead_code)]
    pub fn parse<T: Iterator<Item = String>>(&'a self, args: T) -> Result<R, Error> {
        debug!("starting arg parsing");
        let mut command = self;
        let mut args = args.skip(1).peekable();
        loop {
            if let Some(arg) = args.peek() {
                debug!("checking if {} is a subcommand of {}", arg, command.name);
                let res = command.subcommands.iter().find(|&i| i.name == arg);
                match res {
                    Some(arg) => {
                        // now we need to actually take what was peeked
                        args.next();
                        command = arg;
                    }
                    None => {
                        debug!("{} is not a subcommand, checking if there is a default", arg);
                        match arg.as_str() {
                            // @todo
                            "help" => {}
                            _ => return command.apply(args),
                        }
                    }
                };
            } else {
                debug!("applying command {}", command.name);
                return command.apply(args);
            }
        }
    }

    fn generate_help(&self) -> Value {
        Value::None
    }

    fn get_values_unbounded<T>(&self, arg: &Arg, args: &mut Peekable<T>, est: usize) -> Result<Vec<Value>, Error>
    where
        T: Iterator<Item = String>,
    {
        let target = &arg.value_type;
        let mut params = Vec::with_capacity(est);
        while let Some(param) = args.peek() {
            if param.starts_with("-") {
                break;
            }
            let mut val = cast_type(target, param)?;
            if let Some(validation) = arg.validation {
                debug!("running validation for {:?}", val);
                val = match validation(val) {
                    Ok(v) => v,
                    Err(e) => {
                        debug!("validation failed, reason: {}", e);
                        return Err(Error::InvalidValue(param.clone(), e));
                    }
                };
            }
            params.push(val);
            args.next();
        }
        debug!("found params {:?}", params);
        Ok(params)
    }

    fn get_values_bounded<T>(&self, arg: &Arg, args: &mut Peekable<T>, est: usize) -> Result<Vec<Value>, Error>
    where
        T: Iterator<Item = String>,
    {
        let target = &arg.value_type;
        let mut params = Vec::with_capacity(est);
        let mut j = 0;
        while let Some(param) = args.peek() {
            if param.starts_with("-") || j == est {
                break;
            }
            j += 1;
            let mut val = cast_type(target, param)?;
            if let Some(validation) = arg.validation {
                debug!("running validation for {:?}", val);
                val = match validation(val) {
                    Ok(v) => v,
                    Err(e) => {
                        debug!("validation failed, reason: {}", e);
                        return Err(Error::InvalidValue(param.clone(), e));
                    }
                };
            }
            params.push(val);
            args.next();
        }
        debug!("found params {:?}", params);
        Ok(params)
    }

    fn get_values<T>(&'a self, arg: &'a Arg, args: &mut Peekable<T>) -> Result<Value, Error>
    where
        T: Iterator<Item = String>,
    {
        debug!("getting values for {}", arg.name);
        return match arg.num_values {
            NumValues::Any => Ok(self.get_values_unbounded(arg, args, 0)?.into()),
            NumValues::AtLeast(i) => {
                debug!("looking for at x > {} values", i);
                let params = self.get_values_unbounded(arg, args, 0)?;
                if params.len() >= i {
                    Ok(params.into())
                } else {
                    debug!("too few values found, expected {}, got {}: {:?}", i, params.len(), params);
                    Err(Error::WrongNumValues(arg.name, &arg.num_values, Value::from(params)))
                }
            }
            NumValues::Between(low, high) => {
                debug!("looking for value where {} >= x >= {}", high, low);
                let params = self.get_values_bounded(arg, args, high)?;
                if params.len() >= low && params.len() <= high {
                    Ok(params.into())
                } else {
                    debug!(
                        "wrong number of values found, expected {} >= x >= {}, got {}: {:?}",
                        high,
                        low,
                        params.len(),
                        params
                    );
                    Err(Error::WrongNumValues(arg.name, &arg.num_values, Value::from(params)))
                }
            }
            NumValues::Fixed(i) => {
                debug!("looking for x = {} values", i);
                let mut params = self.get_values_bounded(arg, args, i)?;
                if params.len() != i {
                    debug!("wrong number of found, expected {}, got {}: {:?}", i, params.len(), params);
                    Err(Error::WrongNumValues(arg.name, &arg.num_values, Value::from(params)))
                } else if params.len() == 1 {
                    debug!("single param found, simplifying vec");
                    Ok(params.pop().unwrap())
                } else {
                    Ok(params.into())
                }
            }
            NumValues::None => Ok(Value::None),
        };
    }

    fn handle_arg_missing(&self, arg: &str, out: &mut HashMap<&'a str, Value>) -> Result<(), Error> {
        match arg {
            "--help" | "-h" => {
                out.insert("help", self.generate_help());
                Ok(())
            }
            _ => Err(Error::UnknownArg(String::from(arg))),
        }
    }

    fn handle_arg_inner<T>(&'a self, target: &'a Arg, arg: &str, args: &mut Peekable<T>, out: &mut HashMap<&'a str, Value>) -> Result<(), Error>
    where
        T: Iterator<Item = String>,
    {
        debug!("found arg {} matching {}", target.name, arg);
        out.insert(target.name, self.get_values(target, args)?);
        Ok(())
    }

    fn handle_arg<T>(&'a self, arg: &str, args: &mut Peekable<T>, out: &mut HashMap<&'a str, Value>) -> Result<(), Error>
    where
        T: Iterator<Item = String>,
    {
        if arg.starts_with("--") {
            let arg = arg.trim_start_matches("--");
            debug!("handling long {}", arg);

            for a in &self.args {
                for i in a.long {
                    if i == arg {
                        return self.handle_arg_inner(&a, arg, args, out);
                    }
                }
            }
            self.handle_arg_missing(arg, out)
        } else {
            let arg = arg.trim_start_matches("-");
            debug!("handling short(s) {}", arg);
            let matches = self
                .args
                .iter()
                .filter(|&a| a.short.iter().any(|&i| arg.graphemes(true).any(|g| g == i)))
                .collect::<Vec<&Arg>>();
            match matches.len() {
                0 => {
                    debug!("no arg found for {}, looking for default", arg);
                    match arg {
                        "-h" => {
                            out.insert("help", self.generate_help());
                            Ok(())
                        }
                        _ => Err(Error::UnknownArg(String::from(arg))),
                    }
                }
                1 => {
                    debug!("single short found {}, trying to expand", arg);
                    self.handle_arg_inner(matches[0], arg, args, out)
                }
                _ => {
                    debug!("flag combination found {}", arg);
                    for res in matches {
                        out.insert(res.name, Value::None);
                    }
                    Ok(())
                }
            }
        }
    }

    fn apply<T: Iterator<Item = String>>(&'a self, args: T) -> Result<R, Error> {
        debug!("parsing args using command {}", self.name);
        // @todo: I wonder if we can avoid hashing with compile time magic?
        let mut params: HashMap<&'a str, Value> = HashMap::with_capacity(self.args.len());
        let mut unknown_params = Vec::with_capacity(0);
        let mut positional = Vec::with_capacity(0);
        let mut args = args.peekable();
        while let Some(arg) = args.next() {
            // an argument :O time to start searching!
            if arg.starts_with("-") {
                if arg == "--" {
                    debug!("found --, treating everything after as positional");
                    // doing this inline instead of using a boolean because no point in doing all those "if"s
                    for arg in &mut args {
                        debug!("found positional arg {}", arg);
                        positional.push(arg);
                    }
                }
                debug!("found arg {}", arg);
                match self.handle_arg(&arg, &mut args, &mut params) {
                    Err(Error::UnknownArg(arg)) => unknown_params.push(arg),
                    Err(e) => return Err(e),
                    _ => {}
                }
            } else {
                debug!("found positional arg {}", arg);
                positional.push(arg);
            }
        }
        debug!("finished looping through args, running postprocessing");
        let mut missing = Vec::with_capacity(0);
        for param in &self.args {
            if !params.contains_key(param.name) {
                if let Some(default) = param.default {
                    debug!("using default value for {}", param.name);
                    let val = default();
                    params.insert(param.name, check_type(&param.value_type, &val).map(|_| val)?);
                } else if param.required {
                    missing.push(param.name);
                }
            }
        }
        if !missing.is_empty() {
            debug!("missing required args {:?}", missing);
            return Err(Error::MissingRequiredArgs(missing));
        }
        Ok((self.handler)(Results {
            params,
            unknown_params,
            positional,
        }))
    }
}

#[cfg(test)]
mod tests {
    use std::{convert::TryInto, sync::Once};

    use crate::{value::Type, Arg, Args, Error, NumValues, Value};
    use pretty_assertions::assert_eq;
    use simple_logger::SimpleLogger;

    static INIT: Once = Once::new();

    macro_rules! test {
        ($name:ident() $block:block) => {
            #[test]
            fn $name() {
                INIT.call_once(|| {
                    SimpleLogger::new().init().unwrap();
                });
                $block
            }
        };
    }
    macro_rules! assert_has {
        ($expected:expr, $results:ident, $key:literal) => {
            if let Some(arg) = $results.params.get($key) {
                assert_eq!(Ok($expected), arg.try_into());
                1
            } else {
                0
            }
        };
    }

    test!(test_arg_with_no_value() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| if r.params.contains_key("arg") { 1 } else { 0 },
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg"]));
    });

    test!(test_arg_with_fixed_num_values_fails_on_none() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| if r.params.contains_key("arg") { 1 } else { 0 },
            ..Default::default()
        };
        assert_eq!(
            Err(Error::WrongNumValues("arg", &NumValues::Fixed(1), Value::from(vec![]))),
            args.parse_str(vec!["prog", "--arg"])
        );
    });

    test!(test_arg_with_fixed_num_values() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "lol"]));
    });

    test!(test_arg_with_any_values_none() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::Any,
                ..Default::default()
            }],
            handler: |r| assert_has!(&vec![], r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg"]));
    });

    test!(test_arg_with_any_values_single() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::Any,
                ..Default::default()
            }],
            handler: |r| assert_has!(vec!["lol"], r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "lol"]));
    });

    test!(test_arg_with_any_values_multiple() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::Any,
                ..Default::default()
            }],
            handler: |r| assert_has!(vec!["lol", "lol2"], r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "lol", "lol2"]));
    });

    test!(test_arg_with_fixed_num_values_too_many_values() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg") == 1 && r.positional.first().filter(|i| i.as_str() == "no").is_some(),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse_str(vec!["prog", "--arg", "lol", "no"]));
    });

    test!(test_arg_with_fixed_num_values_and_other_args() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "lol", "--arg2"]));
    });

    test!(test_arg_with_fixed_num_values_and_other_args_double_dash() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "lol", "--arg2"]));
    });

    test!(test_multiple_args() {
        let args = Args {
            args: vec![
                Arg {
                    name: "arg",
                    long: Some("arg"),
                    num_values: NumValues::Fixed(2),
                    ..Default::default()
                },
                Arg {
                    name: "arg2",
                    long: Some("arg2"),
                    num_values: NumValues::None,
                    ..Default::default()
                },
            ],
            handler: |r| match assert_has!(vec!["1", "2"], r, "arg") {
                1 => assert_has!(&Value::None, r, "arg2"),
                _ => 0,
            },
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "1", "2", "--arg2"]));
    });

    test!(test_missing_arg() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| if r.params.contains_key("arg") { 1 } else { 0 },
            ..Default::default()
        };
        assert_eq!(Ok(0), args.parse_str(vec!["prog"]));
    });

    test!(test_sub_command_not_called() {
        let args = Args {
            subcommands: vec![Args {
                name: "sub",
                ..Default::default()
            }],
            handler: |_| 1,
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog"]));
    });

    test!(test_sub_commands() {
        let args = Args {
            subcommands: vec![Args {
                name: "sub",
                subcommands: vec![Args {
                    name: "sub",
                    handler: |_| 1,
                    ..Default::default()
                }],
                ..Default::default()
            }],
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "sub", "sub"]));
    });

    test!(test_default_arg() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                default: Some(|| "lol".into()),
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog"]));
    });

    test!(test_required_arg_missing() {
        let args: Args<()> = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                required: true,
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            ..Default::default()
        };
        assert_eq!(Err(Error::MissingRequiredArgs(vec!["arg"])), args.parse_str(vec!["prog"]));
    });

    test!(test_required_arg() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                required: true,
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "lol"]));
    });

    test!(test_wrong_type() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                value_type: Type::Bool,
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg"),
            ..Default::default()
        };
        assert_eq!(Err(Error::WrongCastType("lol".to_owned())), args.parse_str(vec!["prog", "--arg", "lol"]));
    });

    test!(test_right_type_bool() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                value_type: Type::Bool,
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!(&true, r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "true"]));
    });

    test!(test_right_type_int() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                value_type: Type::Int,
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!(&3, r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "3"]));
    });

    test!(test_right_type_long() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                value_type: Type::Long,
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!(&i64::max_value(), r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", i64::max_value().to_string().as_str()]));
    });

    test!(test_right_type_float() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                value_type: Type::Float,
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!(&f32::MAX, r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", f32::MAX.to_string().as_str()]));
    });

    test!(test_right_type_double() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                value_type: Type::Double,
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!(&f64::MAX, r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", f64::MAX.to_string().as_str()]));
    });

    test!(test_right_type_string() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                value_type: Type::String,
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!("woop", r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "woop"]));
    });

    test!(test_right_type_array() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                value_type: Type::Array(Box::from(Type::Int)),
                ..Default::default()
            }],
            handler: |r| assert_has!(vec![&23, &32], r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "23", "32"]));
    });

    test!(test_right_type_array_single() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                value_type: Type::Array(Box::from(Type::Int)),
                ..Default::default()
            }],
            handler: |r| assert_has!(vec![&23], r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "--arg", "23"]));
    });

    test!(test_wrong_type_array() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                value_type: Type::Array(Box::from(Type::Int)),
                ..Default::default()
            }],
            handler: |r| assert_has!(vec![&23], r, "arg"),
            ..Default::default()
        };
        assert_eq!(Err(Error::WrongCastType("true".to_owned())), args.parse_str(vec!["prog", "--arg", "true"]));
    });

    test!(test_default_returns_wrong_type() {
        let args: Args<()> = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                value_type: Type::Int,
                default: Some(|| "lol".into()),
                ..Default::default()
            }],
            ..Default::default()
        };
        assert_eq!(Err(Error::WrongValueType("lol".into())), args.parse_str(vec!["prog"]));
    });

    test!(test_property() {
        let args = Args {
            handler: |r| r.positional.first().filter(|i| i.as_str() == "prop").is_some(),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse_str(vec!["prog", "prop"]));
    });

    test!(test_property_after_arg() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| r.positional.first().filter(|i| i.as_str() == "prop").is_some(),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse_str(vec!["prog", "--arg", "prop"]));
    });

    test!(test_long_arg_ignores_single_dash() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| !r.params.contains_key("arg"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse_str(vec!["prog", "-arg"]));
    });

    test!(test_short_arg_ignores_mario_kart_double_dash() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| !r.params.contains_key("arg"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse_str(vec!["prog", "--a"]));
    });

    test!(test_short_arg() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| r.params.contains_key("arg"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse_str(vec!["prog", "-a"]));
    });

    test!(test_unicode_short_arg() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("Ẩ"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| r.params.contains_key("arg"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse_str(vec!["prog", "-Ẩ"]));
    });

    test!(test_unicode_short_arg_no_match() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("A"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| r.params.contains_key("arg"),
            ..Default::default()
        };
        assert_eq!(Ok(false), args.parse_str(vec!["prog", "-Ẩ"]));
    });

    test!(test_combinations() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("Ẩ"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg2",
                short: Some("A"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| r.params.contains_key("arg") && r.params.contains_key("arg2"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse_str(vec!["prog", "-ẨA"]));
    });

    test!(test_positional_after_double_dash() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| !r.params.contains_key("arg") && r.positional.first().filter(|f| f.as_str() == "-a").is_some(),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse_str(vec!["prog", "--", "-a"]));
    });

    test!(test_sub_commands_after_arg_is_not_called() {
        let args = Args {
            subcommands: vec![Args {
                name: "sub",
                handler: |_| 1,
                ..Default::default()
            }],
            handler: |_| 0,
            ..Default::default()
        };
        assert_eq!(Ok(0), args.parse_str(vec!["prog", "-arg", "sub"]));
    });

    test!(test_validation() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::Fixed(1),
                validation: Some(|v| {
                    let s: String = (&v).into();
                    if "abc" == s.as_str() {
                        Ok(v)
                    } else {
                        Err("oh noes".to_string())
                    }
                }),
                ..Default::default()
            }],
            handler: |r| !r.params.contains_key("a"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse_str(vec!["prog", "-a", "abc"]));
    });

    test!(test_validation_unbounded() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::Any,
                validation: Some(|v| {
                    let s: String = (&v).into();
                    if "abc" == s.as_str() {
                        Ok(v)
                    } else {
                        Err("oh noes".to_string())
                    }
                }),
                ..Default::default()
            }],
            handler: |r| !r.params.contains_key("a"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse_str(vec!["prog", "-a", "abc"]));
    });

    test!(test_validation_fails() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::Fixed(1),
                validation: Some(|v| {
                    let s: String = (&v).into();
                    if "abc" == s.as_str() {
                        Ok(v)
                    } else {
                        Err("oh noes".to_string())
                    }
                }),
                ..Default::default()
            }],
            handler: |r| !r.params.contains_key("a"),
            ..Default::default()
        };
        assert_eq!(Err(Error::InvalidValue("abcdef".to_string(), "oh noes".to_string())),
            args.parse_str(vec!["prog", "-a", "abcdef"]));
    });

    test!(test_validation_fails_unbounded() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::Any,
                validation: Some(|v| {
                    let s: String = (&v).into();
                    if "abc" == s.as_str() {
                        Ok(v)
                    } else {
                        Err("oh noes".to_string())
                    }
                }),
                ..Default::default()
            }],
            handler: |r| !r.params.contains_key("a"),
            ..Default::default()
        };
        assert_eq!(Err(Error::InvalidValue("abcdef".to_string(), "oh noes".to_string())),
            args.parse_str(vec!["prog", "-a", "abcdef"]));
    });
}
