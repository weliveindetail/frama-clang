struct A { int x; };

void f() { A a; a.x = 0; return; }

int main () {
  f();
  return 0;
}
