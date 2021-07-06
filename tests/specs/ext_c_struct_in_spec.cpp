#include "features.h"

__PUSH_FC_STDLIB


__BEGIN_DECLS

int xxxx;

struct ts { int yyyy; };

/*@ axiomatic np {
      predicate ac{L}(struct ts const *tm) 
               reads xxxx;
   }
*/

/*@ behavior b:
      assumes  nnn: ac(tp);
*/
void m(struct ts const * tp) {}


__END_DECLS
__POP_FC_STDLIB
