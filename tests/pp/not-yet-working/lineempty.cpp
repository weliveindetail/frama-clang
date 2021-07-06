// Tests a line directive that is empty
/*@

requires  \true;
#line
#error "Failure2"

*/
void m() {}
