
int 
(pre(n==0)
post(n==0)
inner)(int n)
{
 return n; 
}



int (pre(n == 0)
      post(n == 0)
      check)(int n)
{
  int q=3; 
  int a=inner(0);
  if(q==4){
    n=3;
    
  } //forces a block idk there should be a better way to do this 
  
  return n; 
}

int main()
{

  //we need to flow forward data
  return check(0);
}
