
//@ ensures \result == (1 ? 2 : 3);
bool empty() { return (1 ? 2 : 3); }

//@ logic integer min(integer x, integer y) = x < y ? x : y;

//@ logic integer max(integer x, integer y) = x < y ? (foo: y): x;

//@ logic integer pos(integer x) = x < 0 ? 0 : foo:x;

//@ logic integer neg(integer x) = x > 0 ? 0 : (foo:x);
