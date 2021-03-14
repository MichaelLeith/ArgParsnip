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
    Array(Box<Type>),
}

impl Default for Type {
    fn default() -> Self {
        Type::Any
    }
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

macro_rules! converters {
    ($x:ty, $into:ident) => {
        impl std::convert::From<$x> for Value {
            fn from(val: $x) -> Self {
                Value::$into(val)
            }
        }

        impl std::convert::TryInto<$x> for Value {
            type Error = Error<'static>;

            fn try_into(self) -> Result<$x, Self::Error> {
                match self {
                    Value::$into(b) => Ok(b),
                    e => Err(Error::WrongValueType(e)),
                }
            }
        }

        impl<'a> std::convert::TryInto<&'a $x> for &'a Value {
            type Error = Error<'static>;

            fn try_into(self) -> Result<&'a $x, Self::Error> {
                match self {
                    Value::$into(b) => Ok(b),
                    e => Err(Error::WrongValueType(e.clone())),
                }
            }
        }

        impl std::convert::TryInto<Vec<$x>> for Value {
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

        impl<'a> std::convert::TryInto<Vec<&'a $x>> for &'a Value {
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

impl std::convert::From<String> for Value {
    fn from(val: String) -> Self {
        Value::String(val)
    }
}

impl<'a> std::convert::Into<String> for &'a Value {
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

impl std::convert::Into<String> for Value {
    fn into(self) -> String {
        match self {
            Value::String(v) => v,
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

impl<'a> std::convert::TryInto<&'a str> for &'a Value {
    type Error = Error<'a>;

    fn try_into(self) -> Result<&'a str, Error<'a>> {
        match self {
            Value::String(b) => Ok(b),
            e => Err(Error::WrongValueType(e.clone())),
        }
    }
}

impl<'a> std::convert::TryInto<Vec<&'a str>> for &'a Value {
    type Error = Error<'a>;

    fn try_into(self) -> Result<Vec<&'a str>, Error<'a>> {
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

impl std::convert::From<&str> for Value {
    fn from(val: &str) -> Self {
        Value::String(val.to_string())
    }
}

macro_rules! cast {
    ($val:ident, $x:ty) => {
        Value::from($val.parse::<$x>().map_err(|_| Error::WrongCastType($val.to_owned()))?)
    };
}

pub(crate) fn check_type(t: &Type, val: &Value) -> Result<(), Error<'static>> {
    match (t, val) {
        (Type::Any, _)
        | (Type::Bool, Value::Bool(_))
        | (Type::Int, Value::Int(_))
        | (Type::Long, Value::Long(_))
        | (Type::Float, Value::Float(_))
        | (Type::Double, Value::Double(_))
        | (Type::String, Value::String(_)) => Ok(()),
        (Type::Array(a), Value::Array(v)) => {
            if v.iter().all(|s| check_type(a, s).is_ok()) {
                Ok(())
            } else {
                Err(Error::WrongValueType(val.clone()))
            }
        }
        _ => Err(Error::WrongValueType(val.clone())),
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
