class A {
  public:
    int foo ();
    int bar () { return this->foo();}
};

int A::foo () { return 0; }

int main() {
  A a;
  a.foo();
  a.bar();
  return 0;
}
