#include <stdio.h>

int (pre(x>0)
    post(forall(x, x>0))
conditions)(int x)
{
    x=x+1;
    return x;
}

int main ()
{ 
    conditions(0);
    return 0;
    // For checking whether we can extract conditions from code
   
}
