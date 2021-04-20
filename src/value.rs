use crate::Error;

use std::{convert::TryInto, fmt::Debug};

#[cfg(feature = "derive")]
use serde::{Deserialize, Serialize};

/// Set of types we support deserializing
#[derive(Debug, PartialEq)]
#[cfg_attr(feature = "derive", derive(Serialize, Deserialize))]
pub enum Type {
    Any,
    Bool,
    Int,
    Long,
    Float,
    Double,
    String,
    Array(Box<Type>),
}

impl Default for Type {
    fn default() -> Self {
        Type::Any
    }
}

/// Actual type we store internally
#[derive(PartialEq, Clone)]
#[cfg_attr(feature = "derive", derive(Serialize, Deserialize))]
pub enum Value {
    None,
    Bool(bool),
    Int(i32),
    Long(i64),
    Float(f32),
    Double(f64),
    String(String),
    Array(Vec<Value>),
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::None => Debug::fmt(&(), f),
            Value::Bool(b) => Debug::fmt(b, f),
            Value::Int(b) => Debug::fmt(b, f),
            Value::Long(b) => Debug::fmt(b, f),
            Value::Float(b) => Debug::fmt(b, f),
            Value::Double(b) => Debug::fmt(b, f),
            Value::String(b) => Debug::fmt(b, f),
            Value::Array(b) => Debug::fmt(b, f),
        }
    }
}

macro_rules! converters {
    ($x:ty, $into:ident) => {
        impl From<$x> for Value {
            fn from(val: $x) -> Self {
                Value::$into(val)
            }
        }

        impl TryInto<$x> for Value {
            type Error = Error<'static>;

            fn try_into(self) -> Result<$x, Self::Error> {
                match self {
                    Value::$into(b) => Ok(b),
                    e => Err(Error::WrongValueType(e)),
                }
            }
        }

        impl<'a> TryInto<&'a $x> for &'a Value {
            type Error = Error<'static>;

            fn try_into(self) -> Result<&'a $x, Self::Error> {
                match self {
                    Value::$into(b) => Ok(b),
                    e => Err(Error::WrongValueType(e.clone())),
                }
            }
        }

        impl TryInto<Vec<$x>> for Value {
            type Error = Error<'static>;

            fn try_into(self) -> Result<Vec<$x>, Self::Error> {
                match self {
                    Value::Array(arr) => {
                        let mut vec = Vec::with_capacity(arr.len());
                        for a in arr {
                            vec.push(a.try_into()?);
                        }
                        Ok(vec)
                    }
                    e => Err(Error::WrongValueType(e)),
                }
            }
        }

        impl<'a> TryInto<Vec<&'a $x>> for &'a Value {
            type Error = Error<'static>;

            fn try_into(self) -> Result<Vec<&'a $x>, Self::Error> {
                match self {
                    Value::Array(arr) => {
                        let mut vec = Vec::with_capacity(arr.len());
                        for a in arr {
                            vec.push(a.try_into()?);
                        }
                        Ok(vec)
                    }
                    e => Err(Error::WrongValueType(e.clone())),
                }
            }
        }
    };
}

converters!(bool, Bool);
converters!(i32, Int);
converters!(i64, Long);
converters!(f32, Float);
converters!(f64, Double);
converters!(Vec<Value>, Array);

impl From<String> for Value {
    fn from(val: String) -> Self {
        Value::String(val)
    }
}

impl<'a> Into<String> for &'a Value {
    fn into(self) -> String {
        match self {
            Value::String(v) => v.clone(),
            Value::None => "".to_string(),
            Value::Bool(v) => v.to_string(),
            Value::Int(v) => v.to_string(),
            Value::Long(v) => v.to_string(),
            Value::Float(v) => v.to_string(),
            Value::Double(v) => v.to_string(),
            Value::Array(v) => v.iter().map(|v| -> String { v.into() }).collect::<String>(),
        }
    }
}

impl Into<String> for Value {
    fn into(self) -> String {
        (&self).into()
    }
}

impl<'a> TryInto<&'a str> for &'a Value {
    type Error = Error<'a>;

    fn try_into(self) -> Result<&'a str, Self::Error> {
        match self {
            Value::String(b) => Ok(b),
            e => Err(Error::WrongValueType(e.clone())),
        }
    }
}

impl<'a> TryInto<Vec<&'a str>> for &'a Value {
    type Error = Error<'a>;

    fn try_into(self) -> Result<Vec<&'a str>, Self::Error> {
        match self {
            Value::Array(arr) => {
                let mut vec = Vec::with_capacity(arr.len());
                for a in arr {
                    vec.push(a.try_into()?);
                }
                Ok(vec)
            }
            e => Err(Error::WrongValueType(e.clone())),
        }
    }
}

impl From<&str> for Value {
    fn from(val: &str) -> Self {
        Value::String(String::from(val))
    }
}

macro_rules! cast {
    ($val:ident, $x:ty) => {
        Value::from($val.parse::<$x>().map_err(|_| Error::WrongCastType(String::from($val)))?)
    };
}

pub(crate) fn check_type(t: &Type, val: &Value) -> bool {
    match (t, val) {
        (Type::Any, _)
        | (Type::Bool, Value::Bool(_))
        | (Type::Int, Value::Int(_))
        | (Type::Long, Value::Long(_))
        | (Type::Float, Value::Float(_))
        | (Type::Double, Value::Double(_))
        | (Type::String, Value::String(_)) => true,
        (Type::Array(a), Value::Array(v)) => v.iter().all(|s| check_type(a, s)),
        _ => false,
    }
}

pub(crate) fn cast_type(t: &Type, val: &str) -> Result<Value, Error<'static>> {
    Ok(match t {
        Type::Bool => cast!(val, bool),
        Type::Int => cast!(val, i32),
        Type::Long => cast!(val, i64),
        Type::Float => cast!(val, f32),
        Type::Double => cast!(val, f64),
        Type::Any | Type::String => Value::from(val.clone()),
        Type::Array(arr) => Value::from(cast_type(arr, val)?),
    })
}
