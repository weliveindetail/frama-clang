/*@ type foo; */

struct A {
  int x;
  //@ logic foo my_foo();
  //@ predicate p(foo f) = \true;
  /*@ class invariant test = p(my_foo()); */
};
