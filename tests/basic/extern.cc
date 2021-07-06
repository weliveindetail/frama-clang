/* run.config
   OPT: @CXX@ -check -print -cxx-demangling-full
*/

extern "C" {
  struct A;
  struct B { int x; };
};

int f(A* x) { return 0;};
int g(B x) { return x.x; }

extern "C" {
  extern "C" struct A* h();
  extern "C" {
    struct C { int y; };
    struct C c = { 1 };
  }
}

extern "C" {
  extern "C++" {
    namespace Foo {
      int foo() { return 0; }
    }
  }
  extern "C" {
    int foo() { return 1; }
  }
}

int main () { return c.y + f(h()) + foo() + Foo::foo(); }
