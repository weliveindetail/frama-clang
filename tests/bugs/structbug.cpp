/* run.config
DONTRUN: ACSLLogicType.cpp needs improvements. See FIXME in handling of TStruct keyword
*/

struct tm { int x; };
class tc  { int y; };
union tu  { int z; float f; };

// The following line should give an error message, or at least a warning
//@ predicate m(class tm s) = \true;
