#![warn(clippy::add_redundant_lifetimes_bound_nested_ref_fn)]
#![warn(clippy::remove_redundant_lifetimes_bound_nested_ref_fn)]

// Code from cve-rs from crates.io, https://github.com/rust-lang/rust/issues/25860
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


// Code from https://github.com/rust-lang/rust/issues/100051
// Duplicated, with/without explicit lifetimes bound:

trait Trait1 {
    type Type1;
}

impl<T1> Trait1 for T1 {
    type Type1 = ();
}

trait Extend1<'a, 'b> {
    fn extend(self, s: &'a str) -> &'b str;
}

// without explicit lifetimes bound
impl<'a, 'b> Extend1<'a, 'b> for <&'b &'a () as Trait1>::Type1 {
    fn extend(self, s: &'a str) -> &'b str {
        s
    }
}

trait Trait2 {
    type Type2;
}

impl<T2> Trait2 for T2 {
    type Type2 = ();
}

trait Extend2<'a, 'b> {
    fn extend(self, s: &'a str) -> &'b str;
}

// with explicit lifetimes bound
impl<'a: 'b, 'b> Extend2<'a, 'b> for <&'b &'a () as Trait2>::Type2 {
    fn extend(self, s: &'a str) -> &'b str {
        s
    }
}

pub fn main2() {
    let y1 = <() as Extend1<'_, '_>>::extend((), &String::from("Hello World"));
    println!("{}", y1);
    // Commented to suppress correct compiler error message:
    // let y2 = <() as Extend2<'_, '_>>::extend((), &String::from("Hello World"));
    // println!("{}", y2);
}
