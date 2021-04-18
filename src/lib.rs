#![cfg_attr(not(feature = "std"), no_std)]
extern crate alloc;

#[cfg(not(feature = "std"))]
mod std;

#[cfg(feature = "derive")]
use serde::{Deserialize, Serialize};

mod value;

use std::iter::Peekable;
use std::string::String;
use std::vec::Vec;
use std::{
    collections::{
        hash_map::Entry::{Occupied, Vacant},
        HashMap,
    },
    process::exit,
};

use crate::value::{cast_type, check_type, Type, Value};
use unicode_segmentation::UnicodeSegmentation;

#[cfg(feature = "debug")]
use log::debug;

#[cfg(not(feature = "debug"))]
macro_rules! debug {
    ($($arg:tt)+) => {};
}

#[derive(PartialEq, Debug)]
pub enum Error<'a> {
    UnknownArg(String),
    InvalidArg,
    MissingRequiredArgs(Vec<&'a str>),
    WrongNumValues(&'a str, &'a NumValues, Value),
    WrongValueType(Value),
    WrongCastType(String),
    InvalidValue(String, String),
    Override(&'a str),
    BadInput,
}

#[allow(dead_code)]
#[derive(PartialEq, Clone, Copy, Debug)]
#[cfg_attr(feature = "derive", derive(Serialize, Deserialize))]
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

#[cfg_attr(feature = "derive", derive(Deserialize))]
pub struct Arg<'a> {
    // unique key (per Args) to identify this arg
    pub name: &'a str,
    // aliases we'll match this arg with e.g -t --test
    #[cfg_attr(feature = "derive", serde(default))]
    pub short: Option<&'a str>,
    #[cfg_attr(feature = "derive", serde(default))]
    pub long: Option<&'a str>,
    // info about this arg
    #[cfg_attr(feature = "derive", serde(default))]
    pub about: &'a str,
    // number of parameters this arg accepts
    #[cfg_attr(feature = "derive", serde(default))]
    pub num_values: NumValues,
    // name for the value of this arg in --help
    #[cfg_attr(feature = "derive", serde(default))]
    pub value_name: Option<&'a str>,
    // default value for this arg
    #[cfg_attr(feature = "derive", serde(skip, default))]
    pub default: Option<fn() -> Value>,
    // whether this arg is required
    #[cfg_attr(feature = "derive", serde(default))]
    pub required: bool,
    // type for values
    #[cfg_attr(feature = "derive", serde(default))]
    pub value_type: Type,
    #[cfg_attr(feature = "derive", serde(skip, default = "default_validation"))]
    pub validation: fn(&Value) -> Result<(), String>,
}

fn default_validation() -> fn(&Value) -> Result<(), String> {
    |_| Ok(())
}

impl<'a> std::default::Default for Arg<'a> {
    fn default() -> Self {
        Arg {
            name: Default::default(),
            short: Default::default(),
            long: Default::default(),
            about: Default::default(),
            num_values: Default::default(),
            value_name: Default::default(),
            default: Default::default(),
            required: Default::default(),
            value_type: Default::default(),
            validation: default_validation(),
        }
    }
}
#[cfg_attr(feature = "debug", derive(Debug))]
#[cfg_attr(feature = "derive", derive(Deserialize))]
pub enum FilterType {
    All,
    Any,
}

#[derive(Default)]
#[cfg_attr(feature = "derive", derive(Deserialize))]
pub struct Filters<'a> {
    #[cfg_attr(feature = "derive", serde(default))]
    pub filter_type: FilterType,
    #[cfg_attr(feature = "derive", serde(default, borrow))]
    pub filters: Vec<Filter<'a>>,
    #[cfg_attr(feature = "derive", serde(default))]
    pub inverse: bool,
}

#[cfg_attr(feature = "debug", derive(Debug))]
#[derive(Default)]
#[cfg_attr(feature = "derive", derive(Deserialize))]
pub struct Filter<'a> {
    #[cfg_attr(feature = "derive", serde(default))]
    pub inverse: bool,
    #[cfg_attr(feature = "derive", serde(default))]
    pub filter_type: FilterType,
    #[cfg_attr(feature = "derive", serde(default, borrow))]
    pub args: Vec<&'a str>,
}

impl<'a> Filter<'a> {
    fn test(&self, builder: &Builder<'a>) -> usize {
        debug!("applying filter {:?} to {:?}", self, builder);
        let res = match self.filter_type {
            FilterType::All => self.args.iter().all(|p| builder.params.contains_key(p) || builder.flags.contains_key(p)),
            FilterType::Any => self.args.iter().any(|p| builder.params.contains_key(p) || builder.flags.contains_key(p)),
        };
        debug!("filter result: {}, using inverse: {}", res, self.inverse);
        (res ^ self.inverse) as usize
    }
}

impl Default for FilterType {
    fn default() -> Self {
        FilterType::Any
    }
}

#[cfg_attr(feature = "derive", derive(Deserialize))]
pub struct Args<'a, T = Results<'a>> {
    pub name: &'a str,
    // @todo: we should support deriving this
    #[cfg_attr(feature = "derive", serde(default))]
    pub path: Option<&'a str>,
    pub version: &'a str,
    #[cfg_attr(feature = "derive", serde(default))]
    pub about: &'a str,
    #[cfg_attr(feature = "derive", serde(default))]
    pub args: Vec<Arg<'a>>,
    #[cfg_attr(feature = "derive", serde(default))]
    pub disable_overrides: bool,
    #[cfg_attr(feature = "derive", serde(default = "default_vec"))]
    pub subcommands: Vec<Args<'a, T>>,
    // handler to invoke when this command has been found.
    // This is not called if a subcommand is invoked
    #[cfg_attr(feature = "derive", serde(skip, bound(deserialize = "T: Handler<'a, T>"), default = "T::handler"))]
    pub handler: fn(Results<'a>) -> T,
    #[cfg_attr(feature = "derive", serde(default))]
    pub filters: Filters<'a>,
}

#[cfg(feature = "derive")]
fn default_vec<'a, T>() -> Vec<Args<'a, T>> {
    vec![]
}

pub trait Handler<'a, T> {
    fn handler() -> fn(Results<'a>) -> T;
}

// @todo: I don't like having this but we can't have negative constraints :/
impl<'a, T: Default> Handler<'a, T> for T {
    fn handler() -> fn(Results<'a>) -> Self {
        |_| Default::default()
    }
}

impl<'a> Handler<'a, Results<'a>> for Results<'a> {
    fn handler() -> fn(Results<'a>) -> Self {
        |results| results
    }
}

impl<'a, T: Handler<'a, T>> Default for Args<'a, T> {
    fn default() -> Self {
        Args {
            name: Default::default(),
            path: Default::default(),
            version: Default::default(),
            about: Default::default(),
            args: Default::default(),
            disable_overrides: Default::default(),
            subcommands: Default::default(),
            handler: T::handler(),
            filters: Default::default(),
        }
    }
}

#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "derive", derive(Deserialize))]
pub struct Results<'a> {
    pub path: &'a str,
    pub flags: HashMap<&'a str, i32>,
    pub params: HashMap<&'a str, Value>,
    pub unknown_params: Vec<String>,
    pub positional: Vec<String>,
}

#[derive(Default, Debug)]
struct Builder<'a> {
    flags: HashMap<&'a str, i32>,
    params: HashMap<&'a str, Value>,
}

pub trait IntoStr {
    fn into(&self) -> &str;
}

impl IntoStr for &str {
    fn into(&self) -> &str {
        self
    }
}

impl IntoStr for String {
    fn into(&self) -> &str {
        self.as_str()
    }
}

trait ArgsMethods<'a, R, S: IntoStr, T: Iterator<Item = S>> {
    fn get_values_unbounded(&self, arg: &Arg, args: &mut Peekable<T>, est: usize) -> Result<Vec<Value>, Error>;
    fn get_values_bounded(&self, arg: &Arg, args: &mut Peekable<T>, est: usize) -> Result<Vec<Value>, Error>;
    fn update_values(&'a self, arg: &'a Arg, args: &mut Peekable<T>, out: &mut Builder<'a>) -> Result<(), Error>;
    fn handle_arg_inner(&'a self, target: &'a Arg, args: &mut Peekable<T>, out: &mut Builder<'a>) -> Result<(), Error>;
    fn handle_arg(&'a self, arg: &str, args: &mut Peekable<T>, out: &mut Builder<'a>) -> Result<(), Error>;
    fn apply(&'a self, args: T) -> Result<R, Error>;
}

impl<'a, R, S: IntoStr, T: Iterator<Item = S>> ArgsMethods<'a, R, S, T> for Args<'a, R> {
    fn get_values_unbounded(&self, arg: &Arg, args: &mut Peekable<T>, est: usize) -> Result<Vec<Value>, Error> {
        let mut params = Vec::with_capacity(est);
        while let Some(param) = args.peek() {
            let param = param.into();
            if param.starts_with("-") {
                break;
            }
            let val = cast_type(&arg.value_type, param)?;
            if let Err(e) = (arg.validation)(&val) {
                debug!("validation failed, reason: {}", e);
                return Err(Error::InvalidValue(param.to_string(), e));
            }
            params.push(val);
            args.next();
        }
        debug!("found params {:?}", params);
        Ok(params)
    }

    fn get_values_bounded(&self, arg: &Arg, args: &mut Peekable<T>, est: usize) -> Result<Vec<Value>, Error> {
        let mut params = Vec::with_capacity(est);
        while let Some(param) = args.peek() {
            let param = param.into();
            if param.starts_with("-") || params.len() == est {
                break;
            }
            let val = cast_type(&arg.value_type, param)?;
            if let Err(e) = (arg.validation)(&val) {
                debug!("validation failed, reason: {}", e);
                return Err(Error::InvalidValue(param.to_string(), e));
            }
            params.push(val);
            args.next();
        }
        debug!("found params {:?}", params);
        Ok(params)
    }

    fn update_values(&'a self, arg: &'a Arg, args: &mut Peekable<T>, out: &mut Builder<'a>) -> Result<(), Error> {
        debug!("getting values for {}", arg.name);
        let res = match arg.num_values {
            NumValues::Any => Ok(self.get_values_unbounded(arg, args, 0)?.into()),
            NumValues::AtLeast(i) => {
                debug!("looking for at x > {} values", i);
                let params = self.get_values_unbounded(arg, args, i)?;
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
            NumValues::None => return self.try_insert_flag(arg.name, out),
        };
        self.try_insert_param(arg.name, res?, out)
    }

    fn handle_arg_inner(&'a self, target: &'a Arg, args: &mut Peekable<T>, out: &mut Builder<'a>) -> Result<(), Error> {
        debug!("found arg {}", target.name);
        self.update_values(target, args, out)
    }

    fn handle_arg(&'a self, arg: &str, args: &mut Peekable<T>, out: &mut Builder<'a>) -> Result<(), Error> {
        if arg.starts_with("--") {
            let arg = &arg[2..];
            debug!("handling long {}", arg);
            for a in &self.args {
                if let Some(i) = a.long {
                    if i == arg {
                        return self.handle_arg_inner(&a, args, out);
                    }
                }
            }
            self.handle_arg_missing(arg, out)
        } else {
            let arg = &arg[1..];
            debug!("handling short(s) {}", arg);
            let mut matches = arg
                .graphemes(true)
                .filter_map(|g| self.args.iter().filter(|a| a.short.is_some()).find(|a| a.short.unwrap() == g));
            match (matches.next(), matches.next()) {
                (Some(first), None) => {
                    debug!("single short found {}, trying to expand", arg);
                    self.handle_arg_inner(first, args, out)
                }
                (Some(first), Some(second)) => {
                    debug!("flag combination found {}", arg);
                    self.try_insert_flag(first.name, out)?;
                    self.try_insert_flag(second.name, out)?;
                    for res in matches {
                        self.try_insert_flag(res.name, out)?;
                    }
                    Ok(())
                }
                (None, _) => {
                    debug!("no arg found for {}, looking for default", arg);
                    self.handle_arg_missing(arg, out)
                }
            }
        }
    }

    fn apply(&'a self, args: T) -> Result<R, Error> {
        debug!("parsing args using command {}", self.name);
        // @todo: I wonder if we can avoid hashing with compile time magic?
        let mut builder = Builder {
            params: HashMap::new(),
            flags: HashMap::new(),
        };
        let mut unknown_params = Vec::with_capacity(0);
        let mut positional = Vec::with_capacity(0);
        let mut args = args.peekable();
        while let Some(arg) = args.next() {
            let arg = (&arg).into();
            // an argument :O time to start searching!
            if arg.starts_with("-") {
                if arg == "--" {
                    debug!("found --, treating everything after as positional");
                    (&mut args).for_each(|a| positional.push((&a).into().to_string()));
                } else {
                    debug!("found arg {}", arg);
                    match self.handle_arg(&arg, &mut args, &mut builder) {
                        Err(Error::UnknownArg(arg)) => unknown_params.push(arg),
                        Err(e) => return Err(e),
                        _ => {}
                    }
                }
            } else {
                debug!("found positional arg {}", arg);
                positional.push(arg.to_string());
            }
        }
        debug!("finished looping through args, running postprocessing");
        // @todo: is there a way we can make this opt-in?
        let mut missing = Vec::with_capacity(0);
        for param in self.args.iter().filter(|p| p.num_values != NumValues::None) {
            if param.required && !builder.params.contains_key(param.name) {
                missing.push(param.name);
            } else if let Some(default) = &param.default {
                if let Vacant(v) = builder.params.entry(param.name) {
                    debug!("using default value for {}", param.name);
                    let val = v.insert(default());
                    if !check_type(&param.value_type, val) {
                        return Err(Error::WrongValueType(val.clone()));
                    }
                }
            }
        }
        if !missing.is_empty() {
            debug!("missing required args {:?}", missing);
            return Err(Error::MissingRequiredArgs(missing));
        }

        if !self.filters.filters.is_empty() {
            let is_ok = match self.filters.filter_type {
                FilterType::All => self.filters.filters.iter().all(|f| f.test(&builder) == 1),
                FilterType::Any => self.filters.filters.iter().any(|f| f.test(&builder) == 1),
            };
            debug!("filter result: {}, using inverse: {}", is_ok, self.filters.inverse);
            if is_ok == self.filters.inverse {
                debug!("filtering failed");
                return Err(Error::BadInput);
            }
        }

        Ok((self.handler)(Results {
            path: self.path.unwrap_or(self.name),
            flags: builder.flags,
            params: builder.params,
            unknown_params,
            positional,
        }))
    }
}

impl<'a, R> Args<'a, R> {
    #[allow(dead_code)]
    pub fn parse<S: IntoStr, T: IntoIterator<Item = S>>(&'a self, args: T) -> Result<R, Error<'a>> {
        debug!("starting arg parsing");
        let mut command = self;
        let mut args = args.into_iter().skip(1).peekable();
        while let Some(arg) = args.peek() {
            let arg = arg.into();
            debug!("checking if {} is a subcommand of {}", arg, command.name);
            if let Some(arg) = command.subcommands.iter().find(|&i| i.name == arg) {
                // now we need to actually take what was peeked
                args.next();
                command = arg;
            } else if arg == "help" {
                print!("{}", command.generate_help());
                exit(0);
                // @todo
            } else if arg == "version" {
                println!("{} {}", command.name, command.version);
                exit(0)
            } else {
                break;
            }
        }
        debug!("applying command {}", command.name);
        return command.apply(args);
    }

    /*
      Format:
         ${about}

         USAGE:
            ${name} [SUBCOMMAND] [OPTIONS]
         OPTIONS:
            ${short}, ${long} ${value_name} ${num_values} ${about}
            -h, --help Prints help information
         SUBCOMMANDS (use ${name} ${subcommand} ${help} for more details):
            ${name} - ${about}
    */
    fn generate_help(&self) -> String {
        // @todo: need to include parents name, e.g prog sub --helps
        let mut help = format!(
            "{}\nUSAGE:\n\t{} [SUBCOMMAND] [OPTIONS]\nOPTIONS:\n",
            self.about,
            self.path.unwrap_or(self.name)
        );
        help.push_str("\t-V, --version Print version info and exit\n");
        if !self.args.is_empty() {
            help = self.args.iter().fold(help, |mut opt, arg| {
                let has_comma = if arg.short.is_some() && arg.long.is_some() { 1 } else { 0 };
                // @todo: factor in num_values
                let size = arg.short.map_or(0, |s| s.len() + 2)
                    + arg.long.map_or(0, |s| s.len() + 3)
                    + has_comma
                    + arg.value_name.map_or(0, |s| s.len() + 1)
                    + arg.about.len();
                opt.reserve(size + 2);
                opt.push_str("\t");
                if let Some(s) = arg.short {
                    opt.push('-');
                    opt.push_str(s);
                    if has_comma == 1 {
                        opt.push(',');
                    }
                    opt.push(' ');
                }
                if let Some(s) = arg.long {
                    opt.push_str("--");
                    opt.push_str(s);
                    opt.push(' ');
                }
                if let Some(s) = arg.value_name {
                    opt.push_str(s);
                    opt.push(' ');
                }
                opt.push_str(arg.about);
                opt.push('\n');
                opt
            });
        }
        help.push_str("\t-h, --help Prints help information\n");
        if !self.subcommands.is_empty() {
            help.push_str("SUBCOMMANDS (use ");
            help.push_str(self.name);
            help.push_str(" [SUBCOMMAND] help for more details):\n");
            help = self.subcommands.iter().fold(help, |mut opt, arg| {
                let size = arg.name.len() + 1 + arg.about.len();
                opt.reserve(size + 1);
                opt.push_str(arg.name);
                opt.push(' ');
                opt.push_str(arg.about);
                opt.push('\n');
                opt
            });
        }
        help
    }

    fn try_insert_param(&self, key: &'a str, value: Value, out: &mut Builder<'a>) -> Result<(), Error> {
        if !self.disable_overrides {
            out.params.insert(key, value);
            return Ok(());
        }
        match out.params.entry(key) {
            Occupied(_) => Err(Error::Override(key)),
            Vacant(e) => {
                e.insert(value);
                Ok(())
            }
        }
    }

    fn try_insert_flag(&self, key: &'a str, out: &mut Builder<'a>) -> Result<(), Error> {
        debug!("inserting flag {}", key);
        match out.flags.entry(key) {
            Occupied(mut e) => {
                if self.disable_overrides {
                    Err(Error::Override(key))
                } else {
                    debug!("incrementing count {}", e.get());
                    e.insert(e.get() + 1);
                    Ok(())
                }
            }
            Vacant(e) => {
                debug!("new flag found");
                e.insert(1);
                Ok(())
            }
        }
    }

    fn handle_arg_missing(&self, arg: &str, _: &mut Builder<'a>) -> Result<(), Error> {
        match arg {
            "help" | "h" => {
                print!("{}", self.generate_help());
                exit(0);
            }
            "version" | "V" => {
                println!("{} {}", self.name, self.version);
                exit(0);
            }
            _ => Err(Error::UnknownArg(String::from(arg))),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, convert::TryInto, sync::Once};

    use crate::{value::Type, Arg, Args, Error, Filter, FilterType, Filters, NumValues, Results, Value};
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

    test!(test_returning_results() {
        let args = Args {
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
        let mut flags = HashMap::with_capacity(1);
        flags.insert("arg", 1);

        assert_eq!(Ok(Results {
            path: "main/sub",
            flags,
            params: HashMap::new(),
            unknown_params: vec!["u".to_string()],
            positional: vec!["lol".to_string()],
        }), args.parse(vec!["prog", "sub", "--arg", "lol", "-u"]));
    });

    test!(test_flag() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| if r.flags.contains_key("arg") { 1 } else { 0 },
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg"]));
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
            args.parse(vec!["prog", "--arg"])
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "lol"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "lol"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "lol", "lol2"]));
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
        assert_eq!(Ok(true), args.parse(vec!["prog", "--arg", "lol", "no"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "lol", "--arg2"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "lol", "--arg2"]));
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
                    num_values: NumValues::Any,
                    ..Default::default()
                },
            ],
            handler: |r| match assert_has!(vec!["1", "2"], r, "arg") {
                1 => assert_has!(&vec![], r, "arg2"),
                _ => 0,
            },
            ..Default::default()
        };
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "1", "2", "--arg2"]));
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
        assert_eq!(Ok(0), args.parse(vec!["prog"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "sub", "sub"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog"]));
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
        assert_eq!(Err(Error::MissingRequiredArgs(vec!["arg"])), args.parse(vec!["prog"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "lol"]));
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
        assert_eq!(Err(Error::WrongCastType("lol".to_owned())), args.parse(vec!["prog", "--arg", "lol"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "true"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "3"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", i64::max_value().to_string().as_str()]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", f32::MAX.to_string().as_str()]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", f64::MAX.to_string().as_str()]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "woop"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "23", "32"]));
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
        assert_eq!(Ok(1), args.parse(vec!["prog", "--arg", "23"]));
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
        assert_eq!(Err(Error::WrongCastType("true".to_owned())), args.parse(vec!["prog", "--arg", "true"]));
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
        assert_eq!(Err(Error::WrongValueType("lol".into())), args.parse(vec!["prog"]));
    });

    test!(test_property() {
        let args = Args {
            handler: |r| r.positional.first().filter(|i| i.as_str() == "prop").is_some(),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse(vec!["prog", "prop"]));
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
        assert_eq!(Ok(true), args.parse(vec!["prog", "--arg", "prop"]));
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
        assert_eq!(Ok(true), args.parse(vec!["prog", "-arg"]));
    });

    test!(test_short_arg_ignores_mario_kart_double_dash() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| !r.flags.contains_key("arg"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse(vec!["prog", "--a"]));
    });

    test!(test_short_arg() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| r.flags.contains_key("arg"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse(vec!["prog", "-a"]));
    });

    test!(test_unicode_short_arg() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("Ẩ"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| r.flags.contains_key("arg"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse(vec!["prog", "-Ẩ"]));
    });

    test!(test_unicode_short_arg_no_match() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("A"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| r.flags.contains_key("arg"),
            ..Default::default()
        };
        assert_eq!(Ok(false), args.parse(vec!["prog", "-Ẩ"]));
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
            handler: |r| r.flags.contains_key("arg") && r.flags.contains_key("arg2"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse(vec!["prog", "-ẨA"]));
    });

    test!(test_flag_repeats() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                long: Some("arg"),
                short: Some("A"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| r.flags["arg"],
            ..Default::default()
        };
        assert_eq!(Ok(4), args.parse(vec!["prog", "-AA", "--arg", "-A"]));
    });

    test!(test_positional_after_double_dash() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg2",
                short: Some("b"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            handler: |r| r.flags.contains_key("arg2") && !r.flags.contains_key("arg") && r.positional.first().filter(|f| f.as_str() == "-a").is_some(),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse(vec!["prog", "-b", "--", "-a"]));
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
        assert_eq!(Ok(0), args.parse(vec!["prog", "-arg", "sub"]));
    });

    test!(test_validation() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::Fixed(1),
                validation: |v| {
                    let s: String = v.into();
                    if "abc" == s.as_str() {
                        Ok(())
                    } else {
                        Err("oh noes".to_string())
                    }
                },
                ..Default::default()
            }],
            handler: |r| !r.params.contains_key("a"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse(vec!["prog", "-a", "abc"]));
    });

    test!(test_validation_unbounded() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::Any,
                validation: |v| {
                    let s: String = v.into();
                    if "abc" == s.as_str() {
                        Ok(())
                    } else {
                        Err("oh noes".to_string())
                    }
                },
                ..Default::default()
            }],
            handler: |r| !r.params.contains_key("a"),
            ..Default::default()
        };
        assert_eq!(Ok(true), args.parse(vec!["prog", "-a", "abc"]));
    });

    test!(test_validation_fails() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::Fixed(1),
                validation: |v| {
                    let s: String = v.into();
                    if "abc" == s.as_str() {
                        Ok(())
                    } else {
                        Err("oh noes".to_string())
                    }
                },
                ..Default::default()
            }],
            handler: |r| !r.params.contains_key("a"),
            ..Default::default()
        };
        assert_eq!(Err(Error::InvalidValue("abcdef".to_string(), "oh noes".to_string())),
        args.parse(vec!["prog", "-a", "abcdef"]));
    });

    test!(test_validation_fails_unbounded() {
        let args = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::Any,
                validation: |v| {
                    let s: String = v.into();
                    if "abc" == s.as_str() {
                        Ok(())
                    } else {
                        Err("oh noes".to_string())
                    }
                },
                ..Default::default()
            }],
            handler: |r| !r.params.contains_key("a"),
            ..Default::default()
        };
        assert_eq!(Err(Error::InvalidValue("abcdef".to_string(), "oh noes".to_string())),
        args.parse(vec!["prog", "-a", "abcdef"]));
    });

    test!(test_fail_duplicate_arg() {
        let args: Args<()> = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            disable_overrides: true,
            ..Default::default()
        };
        assert_eq!(Err(Error::Override("arg")), args.parse(vec!["prog", "-a", "--arg"]));
    });

    test!(test_simple_and_filter() {
        let args: Args<()> = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg2",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            filters: Filters {
                filters: vec![Filter {
                    filter_type: FilterType::All,
                    inverse: false,
                    args: vec!["arg", "arg2"],
                }],
                ..Default::default()
            },
            disable_overrides: true,
            ..Default::default()
        };
        assert_eq!(Ok(()), args.parse(vec!["prog", "-a", "--arg"]));
    });

    test!(test_simple_and_filter_fails() {
        let args: Args<()> = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg2",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            filters: Filters {
                filters: vec![Filter {
                    filter_type: FilterType::All,
                    inverse: false,
                    args: vec!["arg", "arg2"],
                }],
                ..Default::default()
            },
            disable_overrides: true,
            ..Default::default()
        };
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "-a"]));
    });

    test!(test_simple_or_filter() {
        let args: Args<()> = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg2",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            filters: Filters {
                filters: vec![Filter {
                    filter_type: FilterType::All,
                    inverse: true,
                    args: vec!["arg", "arg2"],
                }],
                ..Default::default()
            },
            disable_overrides: true,
            ..Default::default()
        };
        assert_eq!(Ok(()), args.parse(vec!["prog", "-a"]));
    });

    test!(test_simple_or_filter_fails() {
        let args: Args<()> = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg2",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            filters: Filters {
                filters: vec![Filter {
                    filter_type: FilterType::All,
                    inverse: true,
                    args: vec!["arg", "arg2"],
                }],
                ..Default::default()
            },
            disable_overrides: true,
            ..Default::default()
        };
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "-a", "--arg"]));
    });

    test!(test_multiple_filters_any() {
        let args: Args<()> = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg2",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg3",
                long: Some("arg3"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            filters: Filters {
                filters: vec![Filter {
                    filter_type: FilterType::All,
                    inverse: false,
                    args: vec!["arg", "arg2"],
                }, Filter {
                    filter_type: FilterType::All,
                    inverse: false,
                    args: vec!["arg", "arg3"],
                }],
                ..Default::default()
            },
            disable_overrides: true,
            ..Default::default()
        };
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "-a"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg3"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg", "--arg3"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "-a", "--arg"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "-a", "--arg3"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg", "-a"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg3", "-a"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg3", "-a", "--arg"]));
    });

    test!(test_multiple_filters_all() {
        let args: Args<()> = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg2",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg3",
                long: Some("arg3"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            filters: Filters {
                filters: vec![Filter {
                    filter_type: FilterType::All,
                    inverse: false,
                    args: vec!["arg", "arg2"],
                }, Filter {
                    filter_type: FilterType::All,
                    inverse: false,
                    args: vec!["arg", "arg3"],
                }],
                filter_type: FilterType::All,
                ..Default::default()
            },
            disable_overrides: true,
            ..Default::default()
        };
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "-a"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg3"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg", "--arg3"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "-a", "--arg"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "-a", "--arg3"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg", "-a"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg3", "-a"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg3", "-a", "--arg"]));
    });

    test!(test_multiple_filters_all_not() {
        let args: Args<()> = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg2",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg3",
                long: Some("arg3"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            filters: Filters {
                filters: vec![Filter {
                    filter_type: FilterType::All,
                    inverse: false,
                    args: vec!["arg", "arg2"],
                }, Filter {
                    filter_type: FilterType::All,
                    inverse: false,
                    args: vec!["arg", "arg3"],
                }],
                filter_type: FilterType::All,
                inverse: true
            },
            disable_overrides: true,
            ..Default::default()
        };
        assert_eq!(Ok(()), args.parse(vec!["prog", "-a"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg3"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg", "--arg3"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "-a", "--arg"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "-a", "--arg3"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg", "-a"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg3", "-a"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg3", "-a", "--arg"]));
    });

    test!(test_multiple_filters_any_not() {
        let args: Args<()> = Args {
            args: vec![Arg {
                name: "arg",
                short: Some("a"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg2",
                long: Some("arg"),
                num_values: NumValues::None,
                ..Default::default()
            }, Arg {
                name: "arg3",
                long: Some("arg3"),
                num_values: NumValues::None,
                ..Default::default()
            }],
            filters: Filters {
                filters: vec![Filter {
                    filter_type: FilterType::All,
                    inverse: false,
                    args: vec!["arg", "arg2"],
                }, Filter {
                    filter_type: FilterType::All,
                    inverse: false,
                    args: vec!["arg", "arg3"],
                }],
                filter_type: FilterType::Any,
                inverse: true
            },
            disable_overrides: true,
            ..Default::default()
        };
        assert_eq!(Ok(()), args.parse(vec!["prog", "-a"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg3"]));
        assert_eq!(Ok(()), args.parse(vec!["prog", "--arg", "--arg3"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "-a", "--arg"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "-a", "--arg3"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg", "-a"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg3", "-a"]));
        assert_eq!(Err(Error::BadInput), args.parse(vec!["prog", "--arg3", "-a", "--arg"]));
    });
}
