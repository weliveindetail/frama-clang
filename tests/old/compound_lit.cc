/* testing compound lit initialization */
struct A { int x; int y; };

int main() {
  A a;
  a = ((A) { 0, 1 });
  /*@ assert a.x == 0 && a.y == 1; */
  return 0;
}
