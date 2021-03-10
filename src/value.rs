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

// @todo: into
impl std::convert::From<bool> for Value {
    fn from(val: bool) -> Self {
        Value::Bool(val)
    }
}

impl std::convert::From<i32> for Value {
    fn from(val: i32) -> Self {
        Value::Int(val)
    }
}

impl std::convert::From<i64> for Value {
    fn from(val: i64) -> Self {
        Value::Long(val)
    }
}

impl std::convert::From<f32> for Value {
    fn from(val: f32) -> Self {
        Value::Float(val)
    }
}

impl std::convert::From<f64> for Value {
    fn from(val: f64) -> Self {
        Value::Double(val)
    }
}

impl std::convert::From<String> for Value {
    fn from(val: String) -> Self {
        Value::String(val)
    }
}