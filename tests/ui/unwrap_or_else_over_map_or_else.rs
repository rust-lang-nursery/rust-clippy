#![warn(clippy::unwrap_or_else_over_map_or_else)]

fn main() {
    let number = 21;

    let out_put: Result<_, &str> = Ok("foo");
    //should not lint due to type adjustment
    let val_1 = out_put.map_or_else(
        |_| number * 2,
        |v| {
            let c = 2 + 2;
            v.len() + c
        },
    );
    //should lint this
    let val_2 = out_put.map_or_else(|_| number * 2, |v| 3);
    let val_3 = out_put.unwrap_or_else(|d| d);
}
