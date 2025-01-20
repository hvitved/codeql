pub mod nested1 {
    pub mod nested2 {
        pub fn f() {
            println!("nested.rs:nested1::nested2::f");
        }

        fn g() {
            println!("nested.rs:nested1::nested2::g");
            f();
        }
    }

    fn g() {
        println!("nested.rs:nested1::g");
        nested2::f();
    }
}

pub fn g() {
    println!("nested.rs::g");
    nested1::nested2::f();
}
