/* run.config
OPT: @CXX@ @EVA@ -out -journal-disable -print
*/
/*@ behavior default:
    assigns p \from q,p;
    assigns q \from p;
*/
void swap(int& p, int&q);

//@ assigns \result \from \nothing;
int main() {
  int x = 1;
  int y = 2;
  swap(x,y);
  /*@ assert y == 2; */ // must be unknown
  return 0;
}
