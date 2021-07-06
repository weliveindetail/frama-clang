/* run.config
DONTRUN: Not yet fully working
*/
#include <typeinfo>
class C;

const std::type_info& typeID(C* e);
class C {

};

void m(C* c, const std::type_info& cc) {

int i;
i = cc == typeid(*c) ? 2 : 3;
i = cc == typeID(c) ? 2 : 3;
i = cc == typeid(c) ? 2 : 3;
const std::type_info& bt = typeid(*c);
const std::type_info& btt = typeid(C);
const std::type_info& btx = typeid(c);
 
}


