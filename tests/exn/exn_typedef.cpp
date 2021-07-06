namespace plain {

struct A { int x; A(int _x): x(_x) { } };

struct B: public A { B(int _x): A(_x) { } };

typedef B C;

typedef A D;

struct E: public D { E(int _x): D(_x) { } };

int f (int c) {
  try { if(c) throw A(1); else throw C(2); }
  catch (D d) { return d.x; }
}

int g(int c) {
  try { if(c) throw B(1); else throw D(2); }
  catch (A a) { return a.x; }
}

int h(int c) {
  try { if(c) throw C(1); else throw E(2); }
  catch (A a) { return a.x; }
}
}

namespace templated {
template <typename T>struct A { T x; A(T _x):x(_x) { }};
template <typename T>struct B: A<T> { B(T _x): A<T>(_x) { }};

typedef A<int> C;
typedef B<int> D;

int f(int c) {
  try { if (c) throw D(1); else throw B<int>(1); }
  catch (A<int> a) { return a.x; }
}

int g(int c) {
  try { if (c) throw A<int>(1); else throw B<int>(1); }
  catch (C c) { return c.x; }
}
}
