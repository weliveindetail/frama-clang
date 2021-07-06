// BTS 1611

class Point {
        //@ requires 0 == 0;
        void foo() { bar(); }

  void bar() {}

};

class Queue { 
	//  requires 0 < 2;
	void pop(); 
};

//@ requires 0 < 2;
void Queue::pop() { }

void f(int& x);

void f(int &x);

//@ requires x >= 1; ensures x >= 0;
void f(int &x) { x--; }

void h(int& x);

//@ requires x <= 10; ensures x >= \old(x);
void h(int& x);

void h(int &x) { x++; }
