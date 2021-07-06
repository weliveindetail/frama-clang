
class foo {
    int a;
    //@ assigns \result \from *this;
  int bar() { /*@ assert this == this; */ return a; }
};

