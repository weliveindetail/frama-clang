/* run.config
   OPT: @MACHDEP@ @CXX@ -no-remove-exn -print -check
   OPT: @MACHDEP@ @CXX@ -check -print
   OPT: @MACHDEP@ @CXX@ @EVA@
 */
enum foo { BAR = 2 };

int x;
foo y = BAR;

void throw_foo() { throw(BAR); }

void throw_2() { throw(2); }

void throw_foop() { throw(&y); }

void throw_2p() { throw(&x); }

int catch_exn1(void(*f)()) {
  try { f(); }
  catch(foo x) { return 1; }
  catch(int x) { return 0; }
  catch(int* x) { return 2; }
  catch(const foo* x) { return 3; }
  catch(...) { return 4; }
  return 5;
}

int catch_exn2(void(*f)()) {
  try { f(); }
  catch(int x) { return 0; }
  catch(foo x) { return 1; }
  catch(int* x) { return 2; }
  catch(foo* x) { return 3; }
  catch(...) { return 4; }
  return 5;
}


int main() {
  int x,y,z,t;
  x = catch_exn1(throw_foo);
  y = catch_exn1(throw_2);
  z = catch_exn1(throw_foop);
  t = catch_exn1(throw_2p);
  x+= catch_exn2(throw_foo);
  y+= catch_exn2(throw_2);
  z+= catch_exn2(throw_foop);
  t+= catch_exn2(throw_2p);
  return t;
}
