struct foo {
  struct A { int x; };
  enum bla { a,b,c,d };
};

foo::A f() {
  foo::A res = { 0 };
  return res;
}

foo::bla g() {
  foo::bla res = foo::a;
  return res;
}

int main() {
  foo::A a = f();
  /*@ assert a.x == 0; */
  a.x = 42;
  return 0;
}
