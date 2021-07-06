// When this file is run through frama-c as a .c file, an error message
// is issued noting that positive is a predicate, so can't be used as a term.
// However, with frama-clang it translates but fails to prove.

//@ predicate positive(int i) = i > 0;

//@ logic bool p(int i) = i > 0;

/*@ ensures \result <==> positive(k);
    ensures \result == p(k);
*/
bool pos(int k) { return k > 0; }

//@ ensures ko: \result ==  positive(k);
bool m(int k) { return pos(k); }
