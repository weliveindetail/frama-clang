
void decr(void) { throw; }

int main () {
  try {
    try { throw(1); }
    catch (int x) { decr(); } }
  catch (int y) { return y; }
}
