/* run.config
DONTRUN: ACSL parser failure in typeBoolTerm
*/

struct tm { int y; };

//@ assigns !p ? \empty : *p;
void m(struct tm* p) {}
