// run-rustfix

#![warn(clippy::small_underscore_scope)]

struct NewType(u8);

fn main() {
    let n = NewType(24);
    let t = (4, 5);

    let NewType(_) = n;
    let (_, _) = t;
}
