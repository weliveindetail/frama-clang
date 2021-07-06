/* Feature wish: definition of static predicates. */

class Queue {
        static int y;
	int x;
        static int f() { return y; }
	//@ static predicate IsValid() = y>0;

	Queue();
};

//@ ensures Queue::IsValid();
Queue::Queue(){ x = Queue::f() + f(); } 


