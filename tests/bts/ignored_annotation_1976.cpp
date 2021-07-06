
//@ ensures \result * 2 == 222
int area(void) { return 111; }

int main(void) {
    int const a = area();
    //@ assert a == 111;
}

