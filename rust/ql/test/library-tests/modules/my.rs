pub mod nested;

pub fn f() {
    println!("my.rs: f");
}

fn g() {
    f();
}
