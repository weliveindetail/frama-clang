/* run.config
OPT: -wp -wp-msg-key="no-time-info,no-step-info" -wp-cache none @CXX@
*/
class Point2
{
    //@ ensures \result == *this;
    Point2& foo(void) { return *this; }
};

