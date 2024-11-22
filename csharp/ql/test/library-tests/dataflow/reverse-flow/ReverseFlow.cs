public class A
{
    public string Field;

    public A Nested;

    public void M1()
    {
        var a = new A();
        M2(a);
        Sink(a.Nested.Field); // $ MISSING: hasValueFlow=1
    }

    public void M2(A a)
    {
        var b = a.Nested;
        M3(b);
    }

    public void M3(A a)
    {
        a.Field = Source<string>(1);
    }

    public void M4()
    {
        this.M5();
        Sink(this.Nested.Field); // $ MISSING: hasValueFlow=1
    }

    public void M5()
    {
        var b = this.Nested;
        b.M6();
    }

    public void M6()
    {
        this.Field = Source<string>(2);
    }

    public void M7()
    {
        var a = new A();
        M8(a);
        Sink(a.Field); // $ MISSING: hasValueFlow=3
    }

    public void M8(A a)
    {
        var b = new A();
        b.Nested = a;
        M9(b);
    }

    public void M9(A a)
    {
        a.Nested.Field = Source<string>(3);
    }

    public static void Sink(object o) { }

    static T Source<T>(object source) => throw null;
}
