pub mod nested1 {
    pub mod nested2 {
        pub fn f() {
            println!("nested1::nested2::f");
        }

        fn g() {
            f();
        }
    }

    fn g() {
        nested2::f();
    }
}

fn g() {
    nested1::nested2::f();
}
