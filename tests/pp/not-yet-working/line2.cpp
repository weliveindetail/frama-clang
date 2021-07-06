// Tests a line directive with white space after the number
/*@

requires  \true;
#line 101      
#error "Failure2"

*/
void m() {}
