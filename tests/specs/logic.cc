/*@ logic integer f(int x) = x + 1; */

/*@ predicate p{L}(char* x) = \valid(x); 
    predicate foo(int x) = \true;
 */

/*@ lemma f_def: \forall int* x, int *y, z, *t; 
  f(*x) == *x + 1 && f(*y) == *y+1 && f(z) == z+1 && f(*t) == *t+1; */

/*@ lemma f_test: 4 == f((int)3); */

/*@ lemma f_inf: \forall int x; 0 < x <= f(x); */

/*@ logic long long g(long long x) = (long long)(x - 1); */

/*@ behavior default: ensures \result == f(x); */
int g(int x) { return x+1; }


//@ requires foo: p(x);
int h(char* x) { return *x; }
