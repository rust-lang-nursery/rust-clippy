// run-rustfix
#![deny(clippy::option_and_then_some)]

// need a main anyway, use it get rid of unused warnings too
pub fn main() {
    let x = Some(5);
    // the easiest cases
    let _ = x.and_then(Some);
    let _ = x.and_then(|o| Some(o + 1));
    // and an easy counter-example
    let _ = x.and_then(|o| if o < 32 { Some(o) } else { None });
}

pub fn foo() -> Option<String> {
    let x = Some(String::from("hello"));
    Some("hello".to_owned()).and_then(|s| Some(format!("{}{}", s, x?)))
}

pub fn example2(x: bool) -> Option<&'static str> {
    Some("a").and_then(|s| Some(if x { s } else { return None }))
}
