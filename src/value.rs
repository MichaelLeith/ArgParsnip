use crate::Error;

#[derive(Debug, PartialEq)]
pub enum Type {
    Any,
    Bool,
    Int,
    Long,
    Float,
    Double,
    String,
    Array(Box<Type>)
}

#[derive(Debug, PartialEq, Clone)]
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

macro_rules! try_into {
    ($x:ty, $into:ident) => {
        impl std::convert::TryInto<$x> for Value {
            type Error = Error;
        
            fn try_into(self) -> Result<$x, Error> {
                match self {
                    Value::$into(b) => Ok(b),
                    e => Err(Error::WrongValueType(e))
                }
            }
        }

        impl <'a> std::convert::TryInto<&'a $x> for &'a Value {
            type Error = Error;
        
            fn try_into(self) -> Result<&'a $x, Error> {
                match self {
                    Value::$into(b) => Ok(b),
                    e => Err(Error::WrongValueType(e.clone()))
                }
            }
        }

        impl std::convert::TryInto<Vec<$x>> for Value {
            type Error = Error;
        
            fn try_into(self) -> Result<Vec<$x>, Error> {
                match self {
                    Value::Array(arr) => {
                        let mut vec = Vec::with_capacity(arr.len());
                        for a in arr {
                            vec.push(a.try_into()?);
                        }
                        Ok(vec)
                    },
                    e => Err(Error::WrongValueType(e))
                }
            }
        }

        impl <'a> std::convert::TryInto<Vec<&'a $x>> for &'a Value {
            type Error = Error;
        
            fn try_into(self) -> Result<Vec<&'a $x>, Error> {
                match self {
                    Value::Array(arr) => {
                        let mut vec = Vec::with_capacity(arr.len());
                        for a in arr {
                            vec.push(a.try_into()?);
                        }
                        Ok(vec)
                    },
                    e => Err(Error::WrongValueType(e.clone()))
                }
            }
        }
    };
}

macro_rules! from {
    ($x:ty, $into:ident) => {
        impl std::convert::From<$x> for Value {
            fn from(val: $x) -> Self {
                Value::$into(val)
            }
        } 
    };
}

try_into!(bool, Bool);
try_into!(i32, Int);
try_into!(i64, Long);
try_into!(f32, Float);
try_into!(f64, Double);
try_into!(String, String);
try_into!(Vec<Value>, Array);

// @todo: into
from!(bool, Bool);
from!(i32, Int);
from!(i64, Long);
from!(f32, Float);
from!(f64, Double);
from!(String, String);
from!(Vec<Value>, Array);

impl std::convert::From<&str> for Value {
    fn from(val: &str) -> Self {
        Value::String(val.to_string())
    }
}

macro_rules! cast {
    ($val:ident, $x:ty) => {
        Value::from($val.parse::<$x>().map_err(|_| Error::WrongCastType($val))?)
    };
}
pub(crate) fn cast_type(t: &Type, val: String) -> Result<Value, Error> {
    Ok(match t {
        Type::Any => Value::from(val),
        Type::Bool => cast!(val, bool),
        Type::Int => cast!(val, i32),
        Type::Long => cast!(val, i64),
        Type::Float => cast!(val, f32),
        Type::Double => cast!(val, f64),
        Type::String => Value::from(val),
        Type::Array(arr) => Value::from(cast_type(arr, val)?)
    })
}