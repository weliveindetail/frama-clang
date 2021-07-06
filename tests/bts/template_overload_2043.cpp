
template<class Scalar> struct complex {

	//@ requires a == 1;
	complex(Scalar r,int a) { }

	//@  requires a == 2;
	template<class T> complex(T r,int a) { }
};

//@ requires argc <= 6;
int main(int argc,char**argv) {
	complex<char> c('0',argc);
}

