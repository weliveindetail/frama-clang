/* run.config
   OPT: @CXX@ @ALLOC@ -eva-slevel 12 @EVA@ -out -journal-disable -no-annot
*/
class A {
  int val;
  A* next;
 public:
  A(): val(0), next(0) { };
  A(int x, A* tl =0): val(x), next(tl) { };
  A* tl();
  void cons(int x) {
    A* a = new A(this->val, this->next);
    this->val = x;
    this->next = a;
  }
  ~A() { if (next) delete next; }
};

A* A::tl() { return next; }

int main() {
  A a;
  for (int i = 0; i<10; i++) { a.cons(i); }
  A* b = a.tl();
  return 0;
}
