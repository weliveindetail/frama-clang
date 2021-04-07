/* run.config*
EXIT: 1
STDOPT:
*/

// Tests whether define directive is properly reported
/*@

requires  \true;
# define XX 0

*/
void m() {}
