/* run.config
OPT: @MACHDEP@ -deps -print
*/

// Function func should be analysed based on its source definition. Generating
// definitions with default assigns for it caused the misbehavior described in
// the bug report:
// https://git.frama-c.com/pub/frama-c/-/issues/2564
//
// Required preconditions that triggered the misbehavior:
//   - function must be a template
//   - function must be declared before the class used as template parameter
//   - function must access a template member
//   - function must be defined in a namespace
//
namespace test {
  template <class T> T *func(T *foo, int x) {
    foo->add(x);
    return foo;
  }
}

struct Foo {
  int val = 0;
  int get() { return val; }
  void add(int x) { val = x; }
};

int main(int argc, char **argv) {
  Foo foo;
  foo.add(argc);
  return test::func(&foo, argc)->get();
}
