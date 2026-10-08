class C1 {
    init(_ x: Int) {}  // name=C1.init

    convenience init() {  // name=C1.init_conv
        self.init(0)  // $ target=C1.init $ SPURIOUS: target=C1.init_conv
    }
}

var c11 = C1()  // $ type=c11:C1 target=C1.init_conv $ SPURIOUS: target=C1.init
var c12 = C1.init()  // $ type=c12:C1 target=C1.init_conv $ SPURIOUS: target=C1.init

class C2: C1 {}  // inherits `init`

var c21 = C2()  // $ type=c21:C2 $ MISSING: target=C1.init_conv $ SPURIOUS: target=C2.init
var c22 = C2.init()  // $ target=C1.init_conv $ MISSING: type=c22:C2 $ SPURIOUS: target=C1.init

class C3 {
    init() {}
}

var c3 = C3()  // $ type=c3:C3 target=C3.init

class C4: C3 {
    init(_ x: Int) {
        super.init()  // $ target=C3.init
    }

    override convenience init() {
        self.init(0)  // $ target=C4.init
    }
}

class C5: C4 {}  // inherits `init` and `convenience init`

var c51 = C5()  // $ type=c51:C5 $ MISSING: target=C4.init $ SPURIOUS: target=C5.init
var c52 = C5(0)  // $ type=c52:C5 $ MISSING: target=C4.init $ SPURIOUS: target=C5.init

class C6<T1, T2> {
    init(x: T1, y: T2) {}

    private init(s: String) {}

    convenience init(x: T1) {
        fatalError("Convenience initializer not implemented")
    }
}

class C7<T3, T4>: C6<T4, T3> {}  // inherits `init(x: T4, y: T3)` and `convenience init(x: T4)`

var c71 = C7(x: "string", y: true)  // $ type=c71@C7<T3>:Bool type=c71@C7<T4>:String target=C6.init
var c72 = C7<Bool, _>(x: 0)  // $ type=c72@C7<T3>:Bool type=c72@C7<T4>:Int target=C6.init

class C8: C7<Int, String> {  // inherits `init(x: String, y: Int)`
    convenience init(x: String) {  // name=C8.init_conv
        self.init(x: x, y: 0)  // $ target=C6.init
    }
}

struct S1<T> {  // implicit `init(f1: Int = 0, f2: String, f4: Double, f6: Double, f7: Double = 0)`
    var f1: T
    var f2: String = "default"
    var f3: (T) -> T = { $0 }
}

var s11 = S1(f1: 0)  // $ type=s11@S1<T>:Int target=S1.init
var s12 = S1(f1: true, f2: "")  // $ type=s12@S1<T>:Bool target=S1.init
S1(f1: 0, f2: "", f3: { x in x })  // $ type=x:Int target=S1.init
