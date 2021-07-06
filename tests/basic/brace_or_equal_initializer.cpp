class Foo {
public:
    int a { 13 };
    int b { 42 };
    int c = 1337;
    int t[3] {3,4,-1};
    Foo(int x) : a(x) { }
};

int main(void)
{
    Foo x(7);
    return x.b;
}

