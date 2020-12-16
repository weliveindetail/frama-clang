/* run.config
 OPT: @MACHDEP@ @CXX@ -pp-annot -journal-disable -print
*/
/*@ axiom foo: \true;
// just a test for the lexer of annotations
// with two commented lines.
  */

//@ axiom foo1: \true;

int x = 1;

int main () {
  x++;
  return 0;
}
