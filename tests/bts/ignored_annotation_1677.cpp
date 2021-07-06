
    class iterator {
        iterator* current;

        //@ ensures current == (iterator*)0;
        void foo();

public:
      int x;

        //@ ensures current == (iterator*)0;
        iterator bar() {
            foo();
            return *this;
        }

    };
