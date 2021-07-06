class A {
  void (*f) ();
public:
  A( void(*_f)() ) { f = _f; }
  void call() { this->f(); }
};

void foo () { return; }

int main () {
  A a (&foo);
  a.call();
  return 0;
}
