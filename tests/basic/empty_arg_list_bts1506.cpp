extern "C" {

extern void f(void);

}

extern void g(void);

int main() {
  f();
  g();
  return 0;
}
