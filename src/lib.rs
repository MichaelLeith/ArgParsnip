mod value;

use std::{collections::HashMap, env, fmt::Debug, iter::Peekable, usize};
use crate::value::Value;

#[derive(Debug, PartialEq)]
enum Error {
    UnknownArg(String),
    InvalidArg,
    WrongNumValues(String, NumValues, Vec<String>)
}

#[allow(dead_code)]
#[derive(Debug, PartialEq, Clone, Copy)]
enum NumValues {
    None,
    Fixed(usize),
    Any
}

#[derive(Debug)]
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
    default: fn() -> Option<Value>,
    // whether this arg is required
    required: bool
}

impl <'a> std::default::Default for Arg<'a> {
    fn default() -> Self {
        Arg {
            name: "",
            aliases: Vec::with_capacity(0),
            about: "",
            num_values: NumValues::None,
            value_name: None,
            default: || { None },
            required: false
        }
    }
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
    handler: fn(Results) -> T
}

impl<'a, T: Default> std::default::Default for Args<'a, T> {
    fn default() -> Self {
        Args {
            name: "",
            version: "",
            author: "",
            about: "",
            args: Vec::with_capacity(0),
            subcommands: Vec::with_capacity(0),
            handler: |_| Default::default()
        }
    }
}

#[derive(Debug)]
struct ArgResult {
    values: Vec<String>
}

#[derive(Debug)]
struct Results {
    params: HashMap<String, ArgResult>,
    extra: Vec<String>
}

impl std::default::Default for Results {
    fn default() -> Self {
        Results { 
            params: Default::default(), 
            extra: Default::default() 
        }
    }
}

impl<'a, R> Args<'a, R> {
    #[allow(dead_code)]
    pub fn parse<T: Iterator<Item=String> + Debug>(&self, args: T) -> Result<R, Error> {
        let mut command = self;
        let mut args = args.skip(1).peekable();
        loop {
            if let Some(arg) =  args.peek() {
                let res = command.subcommands.iter().find(|&i| i.name == arg);
                match res {
                    Some(arg) => {
                        // now we need to actually take what was peeked
                        args.next(); 
                        command = arg;
                    }
                    None => match arg.as_str() {
                        // @todo
                        "help" => {},
                        _ => return command.apply(args)
                    }
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

    fn generate_help(&self) -> ArgResult {
        ArgResult { values: Default::default() }
    }

    fn handle_arg<T>(&self, arg: &str, args: &mut Peekable<T>) -> Result<(&str, ArgResult), Error>
    where T: Iterator<Item=String> {
        let res = self.args.iter().find(|&a| {
            a.aliases.iter().any(|&i| i == arg)
        });
        match res {
            Some(arg) => {
                let mut params = vec![];
                while let Some(arg) = args.peek() {
                    // @todo: test how this handles quotes
                    if arg.starts_with("-") {
                        break;
                    }
                    params.push(arg.to_string());
                    args.next();
                }
                let expected = match arg.num_values {
                    NumValues::Any => params.len(),
                    NumValues::Fixed(i) => i,
                    NumValues::None => 0
                };
                // @todo: handle defaults
                if params.len() == expected {
                    Ok((arg.name, ArgResult { values: params }))
                } else {
                    Err(Error::WrongNumValues(arg.name.to_owned(), arg.num_values, params))
                }
            },
            None => match arg {
                "--help" | "-h" => Ok(("help", self.generate_help())),
                _ => Err(Error::UnknownArg(arg.to_owned()))
            }
        }
    }

    fn apply<T: Iterator<Item=String>>(&self, args: T) -> Result<R, Error> {
        // @todo: top level args
        let mut params: HashMap<String, ArgResult> = HashMap::with_capacity(self.args.len());
        let mut extra = Vec::with_capacity(0);
        let mut args = args.peekable();
        while let Some(arg) = args.next() {
            // an argument :O time to start searching!
            if arg.starts_with("-") {
                match self.handle_arg(&arg, &mut args) {
                    Ok(result) => {
                        params.insert(result.0.to_owned(), result.1);
                    },
                    Err(Error::UnknownArg(arg)) => extra.push(arg),
                    Err(e) => return Err(e)
                }
            }
            // @todo
        }
        Ok((self.handler)(Results { params, extra }))
    }
}


#[cfg(test)]
mod test {
    use crate::{Args, Arg, Error, NumValues};
    use pretty_assertions::assert_eq;

    #[test]
    fn test_arg_with_no_value() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| if r.params.contains_key("arg") {1} else {0},
            ..Default::default()
        };
        let input = vec!["prog", "-arg"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Ok(1), res); 
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
            handler: |r| if r.params.contains_key("arg") {1} else {0},
            ..Default::default()
        };
        let input = vec!["prog", "-arg"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Err(Error::WrongNumValues("arg".to_owned(), NumValues::Fixed(1), vec![])), res); 
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
            handler: |r| if let Some(arg) = r.params.get("arg") { 
                assert_eq!(arg.values, vec!["lol"]);
                1
            } else {0},
            ..Default::default()
        };
        let input = vec!["prog", "-arg", "lol"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Ok(1), res); 
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
            handler: |r| if let Some(arg) = r.params.get("arg") { 
                assert_eq!(arg.values, Vec::<String>::with_capacity(0));
                1
            } else {0},
            ..Default::default()
        };
        let input = vec!["prog", "-arg"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Ok(1), res); 
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
            handler: |r| if let Some(arg) = r.params.get("arg") { 
                assert_eq!(arg.values, vec!["lol"]);
                1
            } else {0},
            ..Default::default()
        };
        let input = vec!["prog", "-arg", "lol"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Ok(1), res); 
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
            handler: |r| if let Some(arg) = r.params.get("arg") { 
                assert_eq!(arg.values, vec!["lol", "lol2"]);
                1
            } else {0},
            ..Default::default()
        };
        let input = vec!["prog", "-arg", "lol", "lol2"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Ok(1), res); 
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
            handler: |r| if let Some(arg) = r.params.get("arg") { 
                assert_eq!(arg.values, vec!["lol"]);
                1
            } else {0},
            ..Default::default()
        };
        let input = vec!["prog", "-arg", "lol", "no"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Err(Error::WrongNumValues("arg".to_owned(), 
            NumValues::Fixed(1), 
            vec!["lol".to_string(), "no".to_string()])), res); 
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
            handler: |r| if let Some(arg) = r.params.get("arg") { 
                assert_eq!(arg.values, vec!["lol"]);
                1
            } else {0},
            ..Default::default()
        };
        let input = vec!["prog", "-arg", "lol", "-arg2"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Ok(1), res); 
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
            handler: |r| if let Some(arg) = r.params.get("arg") { 
                assert_eq!(arg.values, vec!["lol"]);
                1
            } else {0},
            ..Default::default()
        };
        let input = vec!["prog", "-arg", "lol", "--arg2"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Ok(1), res); 
    }

    #[test]
    fn test_multiple_args() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                aliases: vec!["-arg"],
                num_values: NumValues::Fixed(2),
                ..Default::default()
            }, Arg {
                name: "arg2",
                aliases: vec!["-arg2"],
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| if let Some(arg) = r.params.get("arg") { 
                assert_eq!(arg.values, vec!["1", "2"]);
                if let Some(arg) = r.params.get("arg2") {
                    assert_eq!(arg.values, Vec::<String>::with_capacity(0));
                    1
                } else {
                    0
                }
            } else {0},
            ..Default::default()
        };
        let input = vec!["prog", "-arg", "1", "2", "-arg2"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Ok(1), res); 
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
            handler: |r| if r.params.contains_key("arg") {1} else {0},
            ..Default::default()
        };
        let input = vec!["prog"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Ok(0), res); 
    }

    #[test]
    fn test_sub_command_not_called() {
        let args = Args {
            subcommands: vec![Args {
                name: "sub",
                handler: |_| 0,
                ..Default::default() 
            }],
            handler: |_| 1,
            ..Default::default()
        };
        let input = vec!["prog"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Ok(1), res); 
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
                handler: |_| 0,
                ..Default::default() 
            }],
            handler: |_| 0,
            ..Default::default()
        };
        let input = vec!["prog", "sub", "sub"];
        let res = args.parse(input.into_iter().map(|i| i.to_owned()));
        assert_eq!(Ok(1), res);
    }
}
