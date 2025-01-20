pub mod nested3 {
    pub mod nested4 {
        pub fn f() {
            println!("nested2.rs::nested3::nested4::f");
        }

        pub fn g() {
            println!("nested2.rs::nested3::nested4::g");
        }
    }
}
