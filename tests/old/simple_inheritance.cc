struct Foo {
   int x;
   Foo(int a=0): x(a) {}
}; 

struct A {
   A() {}
}; 

struct B : public A {
   B() {}
}; 

struct C {
   A a;
   C() {}
};

