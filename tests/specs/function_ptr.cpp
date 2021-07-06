typedef void (*fct)(void);

class A {
public:
  fct f;
  static void f1(void) { };
  static void f2(void) { };
  //@ predicate is_valid() = f == f1 || f == f2;
  A(): f(f1) { };
};

A a;
