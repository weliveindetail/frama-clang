namespace C {

  static int i;

  //@ predicate pos(integer k) = k > 0;

};

  //@ predicate pos(integer k) = k < 0;

int i;

void m() {

  C::i = 0;

  i = 0;

  C::i++;

  //@ assert C::pos(C::i);

  i = 1;

  //@ assert pos(-i);

  //@ assert !pos(i);

  //@ assert C::pos(i);

  i = -1;

  //@ assert C::pos(-i);

  //@ assert !(C::pos(i));

}
