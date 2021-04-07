/* run.config*
EXIT: 1
STDOPT:
*/

// Tests a misspelled directive
/*@

requires  \true;
#zzzzz "Failure2"
#error "Line 6"

*/
void m() {}
