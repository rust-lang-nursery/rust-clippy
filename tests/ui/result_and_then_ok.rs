// run-rustfix
#![deny(clippy::result_and_then_ok)]

pub fn main() {
    let x: Result<u32, &str> = Ok(5);
    // the easiest cases
    let _ = x.and_then(Ok);
    let _ = x.and_then(|o| Ok(o + 1));
    // and an easy counter-example
    let _ = x.and_then(|o| if o < 32 { Ok(o) } else { Err("error") });
}

pub fn foo() -> Result<String, ()> {
    let x = Ok(String::from("hello"));
    Ok("hello".to_owned()).and_then(|s| Ok(format!("{}{}", s, x?)))
}

pub fn example2(x: bool) -> Result<&'static str, ()> {
    Ok("a").and_then(|s| Ok(if x { s } else { return Err(()) }))
}
