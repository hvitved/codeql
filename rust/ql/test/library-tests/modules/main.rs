mod my;

use my::*;

use my::nested::nested1::nested2::*;

mod my2;

use my2::*;

use my2::nested2::nested3::nested4::{f, g};

mod m1 {
    fn f() {
        println!("main.rs::m1::f");
    }

    pub mod m2 {
        fn f() {
            println!("main.rs::m1::m2::f");
        }

        pub fn g() {
            println!("main.rs::m1::m2::g");
            f();
            super::f();
        }
    }
}

struct Foo {}

fn h() {
    println!("main.rs::h");

    struct Foo {}

    fn f() {
        struct Foo {}
        println!("main.rs::h::f");
        let _ = Foo {};
    }

    let _ = Foo {};

    f();
}

fn i() {
    let _ = Foo {};
}

fn main() {
    my::nested::nested1::nested2::f();
    my::f();
    nested2::nested3::nested4::f();
    f();
    g();
    h();
    m1::m2::g();
    h();
}
