
class Queue { 

        //@ requires 0<=1;
        void bar() { pop(); }

	//@  requires 0 < 2;
	void pop();

};

//@ requires 0 < 2;
void Queue::pop() { }

