
int(pre(n_inner == 0)
        post(n_inner == 0)
            inner)(int n_inner)
{
  return n_inner;
}

int(pre(n_check == 0)
        post(n_check == 0)
            check)(int n_check)
{
  // n==0 implies 
//let q = 3 in let arg_0 = 0 
  int q = 3;
  //int arg_0=0; //ghost
  
  int a = inner(99);  
  if (q == 4)
  {
    n_check = 3;
  }

  return n_check;
}

int main()
{

  return check(0);
}
