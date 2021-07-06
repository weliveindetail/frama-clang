namespace Z {
  /*@ predicate positive(int i) = i > 0;
   @*/

  bool pos(int i) { return i > 0; }
}

void g(int i) {
   if (i >= 0) {
      //@ assert Z::positive(i);
   int j = 0;
   }
}

//@ requires Z::positive(i);
void f(int i) {
   if (Z::pos(i)) {
   //@ assert i >= 0;
   int j = 0;
   }
}

