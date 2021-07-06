
union _s1 {
	struct _w1 { int t1; } u1;
};

struct _s2 {
	union _w2 { int t2; } u2;
};

union _s3 {
	union _w3 { int t3; } u3;
};


int main() {
    union _s1 v1;
    v1.u1.t1 = 0;
    struct _s2 v2;
    v2.u2.t2 = 0;
    union _s3 v3;
    v3.u3.t3 = 0;
}


