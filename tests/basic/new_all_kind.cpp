class A {
public:
    A() : x(42) {}
    A (int x_) : x(x_) {}
    int x;
};

int main()
{
    A* t = new A[26];
    A* t1 = new A;
    A* t2 = new A();
    A* t3 = new A(5);
    A* t4 = new A[5]();
    return 0;
}
