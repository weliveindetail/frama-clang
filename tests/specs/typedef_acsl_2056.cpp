
class A {
	typedef int value_type;
	int val;

	//@ logic value_type data()        = val;
        //@ ensures \result == data();
	value_type data() { return val; }
};

