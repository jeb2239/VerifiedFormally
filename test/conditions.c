#include <stdio.h>

int main()
{
    // For checking whether we can extract conditions from code
    int x = 1, y = 1, z = 1;
    x=y+1+x;
    pre(x == y);
    while (1) {
        invar(y == z);
    }
    post(z == x);
    return 0;
}
