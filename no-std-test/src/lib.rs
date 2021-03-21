#![no_std]
extern crate alloc;

#[cfg(test)]
mod test {
    use alloc::vec;
    use parsnip::{Arg, Args, NumValues};

    #[test]
    fn test() {
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
    }
}
