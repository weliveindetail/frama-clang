#include "cxx_builtin.cc"
/*@ requires x > 0;
    behavior small:
      assumes x <= 10;
      ensures \result <= 10;
    behavior big:
      assumes x>=10;
      ensures \result >= 10;
*/
int f(int x) {
  if (x < 10) return x+1; else return x;
}

int main() {
  int y = Frama_C_nondet(0,1);
  f(1);
  f(10);
  f(15);
  if(!y) f(y);
  return 0;
}
