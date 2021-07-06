/* run.config
STDOPT: +"-machdep=x86_64 -cpp-extra-args=-DVALUE=~1UL"
STDOPT: +"-machdep=x86_64 -cpp-extra-args=-DVALUE=0x8000000000000000UL"
*/

enum foo {
  A = VALUE
};

int main () {
  return (int)A;
}
