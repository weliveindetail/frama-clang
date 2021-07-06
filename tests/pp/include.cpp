// Tests whether include directive is properly reported -- here the file does not exist
/*@

requires  \true;
# include "asd"

*/
void m() {}
