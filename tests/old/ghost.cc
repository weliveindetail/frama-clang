struct A { int x; };

/*@ ghost struct B { int y; }; */

void f() { /*@ ghost B b1; */ }

int main() {
  /*@ ghost B b; */
  A a;
  /*@ ghost b.y = 0; a.x = b.y; */
  return 0;
}
