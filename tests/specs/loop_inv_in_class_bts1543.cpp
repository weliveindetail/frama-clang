
class int_array3 {
  void foo() {
    //@ loop invariant 0 <= i <= 3;
    for(int i=0; i<3; ++i)
      ;
  }
};

