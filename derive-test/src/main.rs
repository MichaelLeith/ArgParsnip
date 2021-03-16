fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    use parsnip::Args;

    #[test]
    fn test_deserialize() {
        let data = r#"
        {
            "subcommands": [{
                "name": "sub",
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
