mod my;

use my::*;

use my::nested::nested1::nested2::*;

mod my2;

use my2::*;

use my2::nested2::nested3::nested4::{f, g};

mod m1 {}

fn main() {
    my::nested::nested1::nested2::f();
    my::f();
    nested2::nested3::nested4::f();
    f();
    g();
    h();
}
