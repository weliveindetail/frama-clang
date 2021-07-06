#ifndef SM_H
#define SM_H

class Sm
{
public:
        static int cache;

        static int get(void)
        {
        return cache;
        }
};

extern int Sm_get(void);

#endif
