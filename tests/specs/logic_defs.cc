struct A { int x; };
/*@ predicate test(int a, A b) = a == b.x; */
/*@ predicate test2(int a, A b) reads a,b; */
/*@ logic integer test3(int a, A b) = a + b.x; */
/*@ logic integer test4(int a, A b) reads a,b;*/
/*@ logic boolean test5(int a, A b) = a == b.x; */
/*@ lemma foo: \forall int a; \forall A b; test(a,b) <==> test5(a,b); */
int main() {
  A a;
  a.x = 0;
  int x = 0;
  /*@ assert test(x,a) && test2(x,a) && test3(x,a) == test4(x,a); */
  return 0;
}
