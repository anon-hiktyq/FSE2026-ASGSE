
int main()
{
  int i;
  int N=100000;
  int a[2*N+2];

  
            
            /*@
          loop invariant 0 <= i <= N+1 && (\forall int j; 0 <= j <= 2*i ==> a[j] >= 0);
            */
            for(i=0;i<=N;i++) {
    a[2*i]=0;
    a[2*i+1]=0;
  }
            


  
    /*@ assert \forall int i; 0 <= i <= 2*N ==> a[i]>=0; */
  
}
