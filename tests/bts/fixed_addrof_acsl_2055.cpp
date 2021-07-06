
class A {
	int val;

	//@ logic int* data()        = &this->val;
	          int* data() { return &this->val; }
};

