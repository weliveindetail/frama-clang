
template <int N>
class Stack
{
	//@ logic integer Size() = 0;

	//@ logic bool foo1(Stack s) =   Size()  == 0;
	//@ logic bool foo2(Stack s) =   Size(s) == 0;
	//@ logic bool foo3(Stack s) = s.Size()  == 0;

	//@ ensures \result == Size();
	int size() const { return 0; } 
};

Stack
	<6>
	s;

