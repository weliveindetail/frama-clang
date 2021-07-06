struct S { int x; /*@ predicate foo = x >=0; */ };

/*@ predicate foo(integer y) = y>=0; */

extern "C" {
  struct T { int z; };
  
  /*@ predicate bar(integer z) = z < 0; */
  
}
