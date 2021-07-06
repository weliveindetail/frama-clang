// Tests a misspelled directive
/*@

requires  \true;
#   zzzzz "Failure2"
#error "Line 6"
ensures  \true;

*/
void m() {}
