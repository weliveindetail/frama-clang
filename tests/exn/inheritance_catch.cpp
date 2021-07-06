class A { public: int x; A(int _x = 0): x(_x)  { }};
class B: public A { public: B(int _x = 1): A(_x) {} };
class C: public A { public: C(int _x = 2): A(_x) {} };
// NB: B is built before C regardless of the order in which they
// appear in the initializer list in D's constructor.
// See C++11 12.6.2.10 [class.base.init]
class D: public B, public C { public: D(int _x = 3): C(_x), B(_x-1) {} };

void nil() { return; }
void a() { throw(A()); }
void b() { throw(B()); }
void c() { throw(C()); }
void d() { throw(D()); }

void (*p[])() = { nil, a, b, c, d };

int f(int x) {
  if (x < 0 || x > 4) return x;
  try
    { p[x](); }
  catch (C c) { return c.x; }
  catch (B b) { return -b.x; }
  return 10;
}

int main(int c, char** v) {
  if (c<0 || c > 4) return c;
  try
    { int y = f(c); return y + 100; }
  catch(A a) { return a.x + 10; }
}
