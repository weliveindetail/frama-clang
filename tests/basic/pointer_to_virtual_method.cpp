static int g=0;

/**
 * This example shows an error of the
 * handling of pointer to virtual methods.
 * (mbar->*mptr) should call m of Bar
 * but call m of Foo.
 */

class Foo
{
public:
    virtual void m(int i) { g = i; }
};

class Bar : public Foo
{
public:
    virtual void m(int i) { g = 2*i; }
};

int main()
{
    void (Foo::*mptr) (int) = &Foo::m;
    Bar bar;
    Foo* mbar = &bar;
    (mbar->*mptr)(42);
    return g;
}
