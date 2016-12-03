 


int (pre(n == 0)
      post(n == 4)
      check)(int n)
{
    
    if(n==0){
      n=4;
    }
  
  return n;
}

int main()
{
  
  return check(0);
}
