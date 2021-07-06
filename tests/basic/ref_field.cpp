struct S { int& i; S(int &r): i(r) { } S(int *p): i(*p) { }};

struct T { int j; T(int &r): j(r) { }};

void f(int& x) { x++; }

int main () {
  int x = 0;
  T t(x);
  int & y = x;
  S s(y);
  int & z = s.i;
  z = y;
  T t1(t.j);
  S s1(s.i);
  f(x);
  f(t.j);
  if (s1.i == t1.j + 1) return 0; else return 1;
}
