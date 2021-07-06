/* run.config
OPT: @CXX@ -main A::f @EVA@
OPT: @CXX@ -main="A::g(int x)" @EVA@
OPT: @CXX@ -main="::real_main" @EVA@
OPT: @CXX@ -main="real_main" @EVA@
OPT: @CXX@ @EVA@ -main A::h -eva-slevel-function="A::h:3,A::g(int):3" -eva-split-return-function="A::g:-1:1"
*/

namespace A {
  int g(int x) {
    if (x<=0) { return -1; } else { return 1; }
  }

  int g (double y) {
    if (y < 1.) { return 3; } else { return 4; }
  }

  int f(int c) {
    int tmp = g(c);
    tmp += g((double)c);
    return tmp;
  }

  int h(int x) {
    int y = g(x);
    return y+y;
  }

}

int real_main() { return A::f(5); } 
