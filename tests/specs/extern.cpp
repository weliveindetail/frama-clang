/* run.config
OPT: @MACHDEP@ @CXX@ -check -print -cxx-keep-mangling
*/

namespace Foo {
  //@ predicate foo = \true;
}

namespace Bar {
  //@ predicate bar = \true;
  void f() { }
}

extern "C" {

typedef int foo;

const foo f = 42;

/*@ predicate foo(foo x) = x == 0; */

/*@ axiomatic bar {
  predicate bar(foo x);
  axiom Bar_def: \forall foo x; bar(x) <==> x == 0;
  lemma f_bar: !bar(f);
}
*/

/*@ lemma f_prop: !foo(f); */

}
