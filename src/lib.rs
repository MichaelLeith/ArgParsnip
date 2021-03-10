mod value;

use std::{collections::HashMap, env, fmt::Debug, iter::Peekable, usize};
use value::Type;

use crate::value::{cast_type, Value};

#[derive(Debug, PartialEq)]
pub enum Error {
    UnknownArg(String),
    InvalidArg,
    MissingRequiredArgs(Vec<String>),
    // @todo: lets avoid exposing Value here
    WrongNumValues(String, NumValues, Value),
    WrongValueType(Value),
    WrongCastType(String),
}

#[allow(dead_code)]
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum NumValues {
    None,
    Fixed(usize),
    Any,
}

impl Default for NumValues {
    fn default() -> Self {
        NumValues::Any
    }
}

#[derive(Debug, Default)]
struct Arg<'a> {
    // unique key to identify this arg
    name: &'a str,
    // aliases we'll match this arg with e.g -t --test
    aliases: Vec<&'a str>,
    // info about this arg
    about: &'a str,
    // number of parameters this arg accepts
    num_values: NumValues,
    // name for the value of this arg in --help
    value_name: Option<&'a str>,
    // default value for this arg
    default: Option<fn() -> Value>,
    // whether this arg is required
    required: bool,
    // type for values
    value_type: Type,
}

#[derive(Debug)]
struct Args<'a, T> {
    name: &'a str,
    version: &'a str,
    author: &'a str,
    about: &'a str,
    args: Vec<Arg<'a>>,
    subcommands: Vec<Args<'a, T>>,
    // handler to invoke when this command has been found.
    // This is not called if a subcommand is invoked
    handler: fn(Results) -> T,
}

impl<'a, T: Default> std::default::Default for Args<'a, T> {
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
struct Results {
    params: HashMap<String, Value>,
    extra: Vec<String>,
}

impl std::default::Default for Results {
    fn default() -> Self {
        Results {
            params: Default::default(),
            extra: Default::default(),
        }
    }
}

impl<'a, R> Args<'a, R> {
    #[allow(dead_code)]
    pub fn parse_str<'b, T: IntoIterator<Item = &'b str>>(&self, args: T) -> Result<R, Error> {
        self.parse(args.into_iter().map(|a| a.to_string()))
    }

    #[allow(dead_code)]
    pub fn parse<T: Iterator<Item = String>>(&self, args: T) -> Result<R, Error> {
        let mut command = self;
        let mut args = args.skip(1).peekable();
        loop {
            if let Some(arg) = args.peek() {
                let res = command.subcommands.iter().find(|&i| i.name == arg);
                match res {
                    Some(arg) => {
                        // now we need to actually take what was peeked
                        args.next();
                        command = arg;
                    }
                    None => match arg.as_str() {
                        // @todo
                        "help" => {}
                        _ => return command.apply(args),
                    },
                };
            } else {
                return command.apply(args);
            }
        }
    }

    #[allow(dead_code)]
    pub fn env(self) -> Result<R, Error> {
        self.parse(env::args())
    }

    fn generate_help(&self) -> Value {
        Value::None
    }

    fn handle_arg<T>(&self, arg: &str, args: &mut Peekable<T>) -> Result<(&str, Value), Error>
    where
        T: Iterator<Item = String>,
    {
        let res = self.args.iter().find(|&a| a.aliases.iter().any(|&i| i == arg));
        match res {
            Some(arg) => {
                let mut params = vec![];
                let target = &arg.value_type;
                while let Some(arg) = args.peek() {
                    // @todo: test how this handles quotes
                    if arg.starts_with("-") {
                        break;
                    }
                    params.push(cast_type(target, arg.to_string())?);
                    args.next();
                }
                let expected = match arg.num_values {
                    NumValues::Any => params.len(),
                    NumValues::Fixed(i) => i,
                    NumValues::None => 0,
                };
                // @todo: this logic really needs cleaned up
                if params.len() == expected {
                    if expected == 0 {
                        return Ok((arg.name, Value::None));
                    }
                    match &target {
                        Type::Array(_) => Ok((arg.name, Value::from(params))),
                        _ => Ok((arg.name, if expected == 1 { params.pop().unwrap() } else { Value::from(params) })),
                    }
                } else {
                    Err(Error::WrongNumValues(arg.name.to_owned(), arg.num_values, Value::from(params)))
                }
            }
            None => match arg {
                "--help" | "-h" => Ok(("help", self.generate_help())),
                _ => Err(Error::UnknownArg(arg.to_owned())),
            },
        }
    }

    fn apply<T: Iterator<Item = String>>(&self, args: T) -> Result<R, Error> {
        // @todo: top level args
        let mut params: HashMap<String, Value> = HashMap::with_capacity(self.args.len());
        let mut extra = Vec::with_capacity(0);
        let mut args = args.peekable();
        while let Some(arg) = args.next() {
            // an argument :O time to start searching!
            if arg.starts_with("-") {
                match self.handle_arg(&arg, &mut args) {
                    Ok(result) => {
                        params.insert(result.0.to_owned(), result.1);
                    }
                    Err(Error::UnknownArg(arg)) => extra.push(arg),
                    Err(e) => return Err(e),
                }
            }
            // @todo
        }

        let mut missing = Vec::with_capacity(0);
        for param in &self.args {
            if !params.contains_key(param.name) {
                if let Some(default) = param.default {
                    params.insert(param.name.to_owned(), default());
                } else if param.required {
                    missing.push(param.name.to_string());
                }
            }
        }
        if !missing.is_empty() {
            return Err(Error::MissingRequiredArgs(missing));
        }
        Ok((self.handler)(Results { params, extra }))
    }
}

#[cfg(test)]
mod test {
    use std::convert::TryInto;

    use crate::{Arg, Args, Error, NumValues, Value};
    use pretty_assertions::assert_eq;

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

    #[test]
    fn test_arg_with_no_value() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| if r.params.contains_key("arg") { 1 } else { 0 },
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "-arg"]));
    }

    #[test]
    fn test_arg_with_fixed_num_values_fails_on_none() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| if r.params.contains_key("arg") { 1 } else { 0 },
            ..Default::default()
        };
        assert_eq!(
            Err(Error::WrongNumValues("arg".to_owned(), NumValues::Fixed(1), Value::from(vec![]))),
            args.parse_str(vec!["prog", "-arg"])
        );
    }

    #[test]
    fn test_arg_with_fixed_num_values() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "-arg", "lol"]));
    }

    #[test]
    fn test_arg_with_any_values_none() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::Any,
                ..Default::default()
            }],
            handler: |r| assert_has!(&Value::None, r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "-arg"]));
    }

    #[test]
    fn test_arg_with_any_values_single() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::Any,
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "-arg", "lol"]));
    }

    #[test]
    fn test_arg_with_any_values_multiple() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::Any,
                ..Default::default()
            }],
            handler: |r| assert_has!(vec!["lol", "lol2"], r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "-arg", "lol", "lol2"]));
    }

    #[test]
    fn test_arg_with_fixed_num_values_too_many_values() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg"),
            ..Default::default()
        };
        assert_eq!(
            Err(Error::WrongNumValues(
                "arg".to_owned(),
                NumValues::Fixed(1),
                Value::from(vec![Value::from("lol"), Value::from("no")])
            )),
            args.parse_str(vec!["prog", "-arg", "lol", "no"])
        );
    }

    #[test]
    fn test_arg_with_fixed_num_values_and_other_args() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "-arg", "lol", "-arg2"]));
    }

    #[test]
    fn test_arg_with_fixed_num_values_and_other_args_double_dash() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::Fixed(1),
                ..Default::default()
            }],
            handler: |r| assert_has!("lol", r, "arg"),
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "-arg", "lol", "--arg2"]));
    }

    #[test]
    fn test_multiple_args() {
        let args = Args {
            args: vec![
                Arg {
                    name: "arg",
                    aliases: vec!["-arg"],
                    num_values: NumValues::Fixed(2),
                    ..Default::default()
                },
                Arg {
                    name: "arg2",
                    aliases: vec!["-arg2"],
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
        assert_eq!(Ok(1), args.parse_str(vec!["prog", "-arg", "1", "2", "-arg2"]));
    }

    #[test]
    fn test_missing_arg() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| if r.params.contains_key("arg") { 1 } else { 0 },
            ..Default::default()
        };
        assert_eq!(Ok(0), args.parse_str(vec!["prog"]));
    }

    #[test]
    fn test_sub_command_not_called() {
        let args = Args {
            subcommands: vec![Args {
                name: "sub",
                ..Default::default()
            }],
            handler: |_| 1,
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse_str(vec!["prog"]));
    }

    #[test]
    fn test_sub_commands() {
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
    }
}
