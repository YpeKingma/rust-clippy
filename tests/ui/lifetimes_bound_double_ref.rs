#![warn(clippy::lifetimes_bound_double_ref)]

// missing bound
pub fn lifetime_translator_1<'a, 'b, T>(val_a: &'a &'b T, _val_b: &'b T) -> &'a T {
    val_a
}

// with bound
pub fn lifetime_translator_2<'a, 'b: 'a, T>(val_a: &'a &'b T, _val_b: &'b T) -> &'a T {
    val_a
}

fn main() {
    // test code goes here
}
