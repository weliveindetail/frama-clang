/* run.config
EXIT: 1
STDOPT:
*/

// Tests whether define directive is properly reported
/*@

# define XX 0
requires  \true;

*/
void m() {}
