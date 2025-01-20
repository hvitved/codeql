pub mod nested;

use nested::g;

pub fn f() {
    println!("my.rs::f");
}

pub fn h() {
    println!("my.rs::h");
    g();
}
