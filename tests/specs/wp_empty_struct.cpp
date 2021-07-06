/* run.config
OPT: -wp -wp-msg-key="no-time-info,no-step-info" @CXX@
*/
class Point2
{
    //@ ensures \result == *this;
    Point2& foo(void) { return *this; }
};

