/* run.config
DONTRUN: Not yet fully working
*/
struct ts {} *tx;
/*@
assigns tx == 0 ? \empty : { *tx};
assigns tx == 0 ? {*tx} : { *tx};
*/
void m() {}
