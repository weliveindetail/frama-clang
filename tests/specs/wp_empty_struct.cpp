/* run.config
OPT: -wp -wp-msg-key shell -wp-cache none @CXX@
*/
class Point2
{
    //@ ensures \result == *this;
    Point2& foo(void) { return *this; }
};
