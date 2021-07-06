// Tests a line directive with line and file with comment
/*@

requires  \true;
#line 101 "TFILE" // asdasda
#error "Failure2"

*/
void m() {}
