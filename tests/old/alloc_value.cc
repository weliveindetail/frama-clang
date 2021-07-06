/* run.config
STDOPT: +"-no-annot" +"@ALLOC@"
*/

int x = 0;

class A {
  int y;
  /*@ class invariant inv = this->y == 1; */
public:
  A () { x++; y = 1;}
  ~A () { x--; }
};

int main() {
  A* a = new A();
  delete(a);
  /*@ assert x == 0; */
  return 0;
}
