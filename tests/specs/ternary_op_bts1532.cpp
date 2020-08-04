
//@ ensures \result == (x ? 0 : 1);
bool empty(int x) { return (x ? 0 : 1); }

//@ logic integer min(integer x, integer y) = x < y ? x : y;

//@ logic integer max(integer x, integer y) = x < y ? (foo: y): x;

//@ logic integer pos(integer x) = x < 0 ? 0 : foo:x;

//@ logic integer neg(integer x) = x > 0 ? 0 : (foo:x);
