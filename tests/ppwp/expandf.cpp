// Tests whether error PP directive is properly reported
#define MM(X) X OP ONE 
#define OP +
#define NN 45
#define ONE 1
/*@

ensures MM(45) == 46;

*/
void m() {}
