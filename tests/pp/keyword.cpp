// Tests a couple keywords
class A {

   char* p;

//@ class invariant VV = \valid(p);

//@ class invariant NN =  \null != \this ;

};
