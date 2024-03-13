#![warn(clippy::implicit_lifetimes_bound_nested_ref)]
#![warn(clippy::explicit_lifetimes_bound_nested_ref)]

// missing bound
pub fn lifetime_translator_1<'lfta, 'lftb, T>(val_a: &'lfta &'lftb T, _val_b: &'lftb T) -> &'lfta T {
    val_a
}

// with bound
pub fn lifetime_translator_2<'lfta, 'lftb: 'lfta, T>(val_a: &'lfta &'lftb T, _val_b: &'lftb T) -> &'lfta T {
    val_a
}

fn main() {
    // test code goes here
}
