#include <cstdarg>

void foo() { }

void bar() { return; }

void bla(...);

void bli (...);

void bli(...) { }

void f() {

  foo();
  bar();
  bla();
  bla(1);
  bla(1,2);
  bli();
  bli(1);
  bli(1,2);
}
