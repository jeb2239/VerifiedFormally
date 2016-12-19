#include <stdio.h>

int(pre(x > 0)
        post(x>0)
            conditions)(int x)
{
    x = x + 1;
    return x;
}

void (pre(n > 0)
      post(forall(j,implies(j>=0 && j < n,*(a+j)==4)))
      arr_init)(int *a, int n)
{
  int i;
  i=conditions(x);
  for (i = 0; i < n; i++)
  { invar(i != n,
              i >= 0 && i <= n && forall(j, implies(j>=0 && j<i, *(a+j) == 4)),
              i)
    a[i] = 4;
  }

  return;
}

int (
post(x==0)
main)()
{
    
    
    conditions(0);
    //int x=0;
     int arr[5];

  arr_init(&arr[0], 5);
    
    return 0;
    // For checking whether we can extract conditions from code
}
