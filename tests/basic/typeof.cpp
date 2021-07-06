/* run.config
STDOPT: +"-cpp-extra-args=-std=gnu++11" 
*/

unsigned char T=0xFF;
typedef long foo;
typeof (typeof (char *)[4]) y;

int main (){
  
  int G;
  G = static_cast<typeof G>(0xFFFFFFFF);
  //  G += static_cast<typeof foo>(0xFFFFFFFF);
  return G;
}
