typedef unsigned int size_t;

class A {
public:
    void operator delete(void* ptr) { /*std::cout << "delete A" << std::endl;*/ }
    void operator delete[](void* ptr) { /*std::cout << "delete[] A" << std::endl;*/ }
    void* operator new(size_t n) { /*std::cout << "new A" << std::endl;*/ return (A*)1;}
    void* operator new[](size_t n) { /*std::cout << "new[] A" << std::endl;*/ return (A*)2;}
private:
    int _; // avoid empty class
};

class B {
private:
    int _; // avoid empty class
};

int main() {
    A* p1 = new A;
    A* p2 = new A[10];
    B* p3 = new B;
    B* p4 = new B[10];
    int* p5 = new int;
    int* p6 = new int[10];
    delete p1;
    delete[] p2;
    delete p3;
    delete[] p4;
    delete p5;
    delete[] p6;
}

