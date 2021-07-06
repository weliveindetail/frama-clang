
class vector {
    int sz;
    //@ logic int size() = sz;
    int  size() { return sz; }

    //@ requires n < size();
    void foo(int n);
};

