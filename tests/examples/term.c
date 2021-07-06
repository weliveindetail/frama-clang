//@ predicate positive(int i) = i > 0;
//@ logic boolean p(int i) = i > 0;

//@ ensures \result == p(k);
int pos(int k) { return k > 0; }

//@ ensures \result ==  p(k);
int m(int k) { return pos(k); }
