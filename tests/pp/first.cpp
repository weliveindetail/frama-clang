// Tests whether error PP directive is properly reported
// and the annotation kind is properly found when the directcive is first
/*@

#error "Failure2"
requires  \true;

*/
void m() {}
