/* run.config*
EXIT: 1
STDOPT:
*/
// Tests whether pragma directive is properly reported
/*@

requires  \true;
  	# pragma asdasdasd

*/
void m() {}
