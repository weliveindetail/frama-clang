// ACSL allows complete as a behavior name even though it is also a keyword
/*@ 
behavior complete:
requires \true;
complete behaviors;
*/
void m() {}

/*@ 
behavior a:
requires \true;
behavior complete:
requires \true;
complete behaviors complete,a;
disjoint behaviors complete,a;
*/
void mm() {
  //@ for a : assert \true;
  //@ for complete :assert \true;
}
