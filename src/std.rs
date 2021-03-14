#![no_std]

pub mod boxed {
    pub use alloc::boxed::Box;
}

pub mod convert {
    pub use core::convert::From;
    pub use core::convert::TryInto;
}

pub mod collections {
    pub use hashbrown::HashMap;
}

pub mod default {
    pub use core::default::Default;
}

pub mod iter {
    pub use core::iter::Peekable;
}

pub mod fmt {
    pub use alloc::fmt::Debug;
}

pub mod vec {
    pub use alloc::vec::Vec;
}

pub mod string {
    pub use alloc::string::String;
}
