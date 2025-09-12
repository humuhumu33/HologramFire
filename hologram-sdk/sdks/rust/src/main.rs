use std::env;
use std::io::{self, Read, Write};
use std::process::{Command, Stdio};

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).unwrap_or(0);
    let ref_cmd = env::var("HOLOGRAM_SDK_REF").unwrap_or("npx ts-node --transpile-only sdk/ref/cli.ts".to_string());
    let mut parts = ref_cmd.split_whitespace();
    let exe = parts.next().unwrap_or("node");
    let args: Vec<&str> = parts.collect();
    let mut child = Command::new(exe)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn().expect("spawn");

    {
        let stdin = child.stdin.as_mut().unwrap();
        stdin.write_all(input.as_bytes()).unwrap();
    }
    let out = child.wait_with_output().expect("wait");
    io::stdout().write_all(&out.stdout).unwrap();
}
