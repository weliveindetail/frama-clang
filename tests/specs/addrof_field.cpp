struct A {
  int x;
};

/*@ 
  requires \valid(x);
  ensures \initialized(&x->x);
*/
void f(A* x) { x->x = 0; }
