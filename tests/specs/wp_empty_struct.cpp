/* run.config
OPT: @CXX@ @WP@
*/
class Point2
{
    //@ ensures \result == *this;
    Point2& foo(void) { return *this; }
};
