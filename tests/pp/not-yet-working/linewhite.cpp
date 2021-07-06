// Tests a line directive that is just white space
/*@

requires  \true;
#line	   
#error "Failure2"

*/
void m() {}
