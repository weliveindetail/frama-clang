// Tests a line directive that is empty
/*@

requires  \true;
#line // comment
#error "Failure2"

*/
void m() {}
