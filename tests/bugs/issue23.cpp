class C {
public:

  static int i;

};

int i;

void m() {
  C::i = 0;
  i = 0;
  C::i++;
  //@ assert i == 0;
  //@ assert C::i == 1;
}

