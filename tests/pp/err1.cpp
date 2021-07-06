// Tests whether error PP directive is ignored in a regular comment
/* @
requires \true;
#  error "Failure"
#error "Failure2"
#	error "Failure3"

*/
void m() {}
