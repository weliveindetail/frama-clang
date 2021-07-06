void foo() { }

/*@ axiomatic a { 
  logic int foo{L}(int* i); 

  axiom foo_def{L1,L2}:
  \forall int* i,*j; \forall int k; foo{L1}(i) == foo{L2}(j+k);
}
*/

struct Bar { 

  int x;

  /*@ ensures foo(&x) == foo(\at(&x,Pre)); */
  void incr() { x++; }
  
};

