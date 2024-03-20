#![warn(clippy::implicit_lifetimes_bound_nested_ref)]
#![warn(clippy::explicit_lifetimes_bound_nested_ref)]

// issue 25860, missing bound
pub fn lifetime_translator_1<'lfta, 'lftb, T>(val_a: &'lfta &'lftb T, _val_b: &'lftb T) -> &'lfta T {
    val_a
}

// issue 25860, with bound
pub fn lifetime_translator_2<'lfta, 'lftb: 'lfta, T>(val_a: &'lfta &'lftb T, _val_b: &'lftb T) -> &'lfta T {
    val_a
}

// helper declarations for issue 84591
trait Supertrait<'a, 'b> {
    fn convert<T: ?Sized>(x: &'a T) -> &'b T;
}

struct MyStruct;

impl<'a: 'b, 'b> Supertrait<'a, 'b> for MyStruct {
    fn convert<T: ?Sized>(x: &'a T) -> &'b T {
        x
    }
}

trait Subtrait<'a, 'b, R>: Supertrait<'a, 'b> {}

// issue 84591, missing bound:
impl<'a, 'b> Subtrait<'a, 'b, &'b &'a ()> for MyStruct {}

trait Subtrait2<'a, 'b, R>: Supertrait<'a, 'b> {}

// issue 84591, with bound:
impl<'a: 'b, 'b> Subtrait2<'a, 'b, &'b &'a ()> for MyStruct {}

// helper declarations for issue 100051
trait Trait1 {
    type Type1;
}

impl<T1> Trait1 for T1 {
    type Type1 = ();
}

trait Extend1<'a, 'b> {
    fn extend(self, s: &'a str) -> &'b str;
}

// issue 100051, without explicit lifetimes bound
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

// issue 100051, with explicit lifetimes bound
impl<'a: 'b, 'b> Extend2<'a, 'b> for <&'b &'a () as Trait2>::Type2 {
    fn extend(self, s: &'a str) -> &'b str {
        s
    }
}

fn main() {
    // test code goes here
}
