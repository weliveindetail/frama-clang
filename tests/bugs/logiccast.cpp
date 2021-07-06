char* base;

void m(void* r) {
//@ assert \subset(r, (void*)(base + (0..1)));
}
void n(char* r) {
//@ assert \subset(r, (char*)(void*)(base + (0..1)));
}
