use parsnip::Args;

fn main() {
    let data = r#"
    {
        "name": "derive-test",
        "about": "example using serde",
        "version": "1.0",
        "subcommands": [{
            "name": "sub",
            "path": "derive-test sub",
            "version": "0.1",
            "args": [{
                "name": "arg",
                "long": "arg",
                "num_values": "Any"
            }],
            "subcommands": [{
                "name": "sub2",
                "path": "derive-test sub sub2",
                "version": "0.2"
            }]
        }]
    }"#;

    // Parse the string of data into serde_json::Value.
    let args: Args = serde_json::from_str(data).unwrap();
    println!("{:?}", args.parse(std::env::args().into_iter().skip(1)));
}

#[cfg(test)]
mod tests {
    use parsnip::Args;

    #[test]
    fn test_deserialize() {
        let data = r#"
        {
            "name": "derive-test",
            "version": "1.0",
            "subcommands": [{
                "name": "sub",
                "version": "1.0",
                "path": "main/sub",
                "args": [{
                    "name": "arg",
                    "long": "arg",
                    "num_values": "None"
                }]
            }]
        }"#;

        // Parse the string of data into serde_json::Value.
        let _: Args = serde_json::from_str(data).unwrap();
    }
}
