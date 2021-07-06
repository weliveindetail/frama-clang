class C {
  union {
    long raw;
    struct {
      long a: 1;
      long b: 1;
      long nil: sizeof(long) - 2;
    } st;
  };
  long get_b () {
    return this->st.a;
  }
};
