/* run.config
   DONTRUN: needs debugging
*/
class A {
  unsigned int raw;
  public:
    unsigned int get() { return raw; }
}  __attribute__((aligned(sizeof(unsigned int)), packed));


unsigned int f(A&x) { return x.get(); }
