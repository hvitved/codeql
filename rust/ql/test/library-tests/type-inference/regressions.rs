mod regression1 {

    pub struct S<T>(T);

    pub enum E {
        V { vec: Vec<E> },
    }

    impl<T> From<S<T>> for Option<T> {
        fn from(s: S<T>) -> Self {
            Some(s.0) // $ fieldof=S
        }
    }

    pub fn f() -> E {
        let mut vec_e = Vec::new(); // $ target=new
        let mut opt_e = None;

        let e = E::V { vec: Vec::new() }; // $ target=new

        if let Some(e) = opt_e {
            vec_e.push(e); // $ target=push
        }
        opt_e = e.into(); // $ target=into

        #[rustfmt::skip]
        let _ = if let Some(last) = vec_e.pop() // $ target=pop
        {
            opt_e = last.into(); // $ target=into
        };

        opt_e.unwrap() // $ target=unwrap
    }
}

mod regression2 {
    trait SomeTrait {}

    trait MyFrom<T> {
        fn my_from(value: T) -> Self;
    }

    impl<T> MyFrom<T> for T {
        fn my_from(s: T) -> Self {
            s
        }
    }

    impl<T> MyFrom<T> for Option<T> {
        fn my_from(val: T) -> Option<T> {
            Some(val)
        }
    }

    pub struct S<Ts>(Ts);

    pub fn f<T1, T2>(x: T2) -> T2
    where
        T2: SomeTrait + MyFrom<Option<T1>>,
        Option<T1>: MyFrom<T2>,
    {
        let y = MyFrom::my_from(x); // $ target=my_from
        let z = MyFrom::my_from(y); // $ target=my_from
        z
    }
}
