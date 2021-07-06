struct A {
     int& a;
     int b;
};

int main() {
     int x = 0;
     A y = { x, 1 };
     y.a++;
     return x;
}
