#![warn(clippy::add_redundant_lifetimes_bound_double_ref_arg)]

// missing bound
pub fn lifetime_translator_1<'lfta, 'lftb: 'lfta, T>(val_a: &'lfta &'lftb T, _val_b: &'lftb T) -> &'lfta T {
    val_a
}

// with bound
pub fn lifetime_translator_2<'lfta, 'lftb, T>(val_a: &'lfta &'lftb T, _val_b: &'lftb T) -> &'lfta T {
    val_a
}

fn main() {
    // test code goes here
}
