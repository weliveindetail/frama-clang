
class cl {};
int operator==(cl a, cl b) { return 1; }
int operator!=(cl a, cl b) { return !(a == b); }

