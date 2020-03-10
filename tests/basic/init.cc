struct A {
     int& a;
     int b;
};

typedef char myArray[10];

typedef struct myStruct {
   myArray a;
 } myStruct;

myStruct s = {};

int main() {
     int x = 0;
     A y = { x, 1 };
     y.a++;
     return x;
}
