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

        pub mod m3 {
            use super::f;
            pub fn h() {
                println!("main.rs::m1::m2::m3::h");
                f();
            }
        }
    }
}

struct Foo {}

fn h() {
    println!("main.rs::h");

    struct Foo {}

    fn f() {
        use m1::m2::g;
        g();

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

use my2::nested2 as my2_nested2_alias;

use my2_nested2_alias::nested3::{nested4::f as f_alias, nested4::g as g_alias, nested4::*};

fn main() {
    my::nested::nested1::nested2::f();
    my::f();
    nested2::nested3::nested4::f();
    f();
    g();
    h();
    m1::m2::g();
    m1::m2::m3::h();
    h();
    f_alias();
    g_alias();
}
