static int g=0;
void f(int i);

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

void f(int i)
{
    g = i;
}

int main()
{
    void (Foo::*mptr) (int) = &Foo::m;
    Foo obj;
    Foo* p=&obj;
    (obj.*mptr)(12);
    (p->*mptr)(1000);
    void (Bar::*mptr_) (int) = &Bar::m;
    Bar bar;
    (bar.*mptr_)(42);
    return g;
}
