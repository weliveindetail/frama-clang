
extern "C" {

struct A;
struct B { int x; struct A* a; B():x(),a() {}};

};

struct C { int y; struct B b; };

int f(A); int g(C x) { return x.b.x; }

int main () { C y; return g(y); }
