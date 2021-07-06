// Tests whether error PP directive is properly reported
/*@

requires  \true;
#  error "Failure1"
#error "Failure2"

*/
void m() {}
