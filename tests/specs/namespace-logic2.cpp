/* run.config
STDOPT: +"-cxx-demangling-full"
*/
namespace C {

  static int i;
  //@ predicate pos(integer k) = k > 0;

};
  //@ predicate pos(integer k) = k < 0;


void m() {
  //@ assert !pos(1);
  //@ assert !C::pos(-1);
}
