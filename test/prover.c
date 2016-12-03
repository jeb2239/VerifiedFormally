 


int (pre(n == 0)
      post(n == 4)
      check)(int n)
{
    int a=30;
    if(a==0){
      n=4;
    }
  
  return n;
}

int main()
{
  //we need to flow forward data
  return check(0);
}
