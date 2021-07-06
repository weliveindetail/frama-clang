template<class T>class Foo { public: T* x; Foo(T* _x=0): x(_x){ } };
int main() {
  int x;
  Foo<int>foo;
  return 0;
}
