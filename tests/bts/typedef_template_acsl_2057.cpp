
template<typename T> class vector {
    typedef T* pointer;

    pointer buf;

    //@ logic T* begin() = buf;
    //@ logic integer offset(T* i) = i - begin();
    //@ logic pointer begin() = buf;
    //@ logic integer offset(pointer i) = i - begin();
};

vector<int> v;

