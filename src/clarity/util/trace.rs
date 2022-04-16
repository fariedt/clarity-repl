use crate::clarity::Environment;

pub fn call_depth(env: &Environment) -> usize {
    env.call_stack
        .stack
        .iter()
        .filter(|&fnid| fnid.identifier == "_native_:special_contract-call")
        .count()
}

pub fn trace(env: &Environment, fn_name: &str, args: &[String]) {
    if env.global_context.simulate {
        let depth = call_depth(env);
        println!(
            "{}{} -> ({} {}){}",
            "| ".repeat(depth),
            depth + 1,
            fn_name,
            args.join(" "),
            if fn_name != "contract-call?" {
                format!(
                    " ;; .{}",
                    env.contract_context.contract_identifier.name.to_string()
                )
            } else {
                "".to_string()
            },
        )
    }
}
