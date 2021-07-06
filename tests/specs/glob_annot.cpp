namespace Foo {
//@ ghost int x = 1;
/*@ logic integer foo(integer x) = x; */
/*@ requires foo(1) == 1; */
  int f() { return 1; }
}

int f() { return 1; }
