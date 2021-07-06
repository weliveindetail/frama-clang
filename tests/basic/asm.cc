/* Inline assembly */
int main () {
  int temp = 0;
  int usernb = 3;
  __asm__ volatile (
                    "pusha \n"
                    "mov eax, %0 \n"
                    "inc eax \n"
                    "mov ecx, %1 \n"
                    "xor ecx, %1 \n"
                    "mov %1, ecx \n"
                    "mov eax, %1 \n"
                    "popa \n"
                    : // no output
                    : "m" (temp), "m" (usernb) ); // input
   int arg1, arg2, add, sub, mul, quo, rem ;

    arg1 = 1337;
    arg2 = 42;

    __asm__ volatile ( "addl %%ebx, %%eax;"
            : "=a" (add)
            : "a" (arg1) , "b" (arg2) );
    __asm__ ( "subl %%ebx, %%eax;"
            : "=a" (sub));
    __asm__ ( "imull %%ebx, %%eax;"
            : "=a" (mul)
            : "a" (arg1) , "b" (arg2)
            : "edx");

    __asm__ ( "movl $0x0, %%edx;"
              "movl %2, %%eax;"
              "movl %3, %%ebx;"
              "idivl %%ebx;"
              : "=a" (quo), "=d" (rem)
              : "g" (arg1), "g" (arg2) );

    return rem*10000+add*1000+sub*100+mul*10+quo;
};
