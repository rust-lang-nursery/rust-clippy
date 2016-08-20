#![feature(plugin)]
#![plugin(clippy)]
#![deny(cmp_null)]

fn main() {
    let x = 0;
    let p : *const usize = &x;
    if p == ptr::null() { //~ERROR:  Comparing with null
        println!("This is surprising!");
    }
    let mut y = 0;
    let mut m : *mut usize = &mut y;
    if m == ptr::null_nut() { //~ERROR:  Comparing with null
        println!("This is surprising, too!");
    }
}
