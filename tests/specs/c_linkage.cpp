
extern "C" {

/*@ ensures \valid((char*)\result + (0..size)); */
void *malloc(unsigned int size);

}
