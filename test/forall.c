#include <stdio.h>

int (pre(x>0)
    post(forall(x, x>0))
conditions)(int x)
{
    int x = 1, y = 1, z = 1;
    x=y+1+x;
    return 0;
}

int main ()
{
    conditions(0);
    return 0;
    // For checking whether we can extract conditions from code
   
}
