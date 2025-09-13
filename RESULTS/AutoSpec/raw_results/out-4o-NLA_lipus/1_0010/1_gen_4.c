/*@ requires a>=n && n==0;*/
void main1(int a,int n){
 
  int x,y,z;
  
  x=0;
  y=1;
  z=6;
  

  /*@
  loop invariant x == n * n * n;
  loop invariant y == 3 * n * n + 3 * n + 1;
  loop invariant z == 6 * n + 6;
  loop invariant n <= a + 1;
  loop invariant 0 <= n <= a + 1;
  loop invariant n >= 0;
  loop invariant a >= n;
  loop invariant z % 6 == 0;
  loop invariant y >= 1;
  loop invariant \forall integer k; 0 <= k < n ==> x >= k * k * k;
  loop invariant \forall integer k; 0 <= k < n ==> y >= 3 * k * k + 3 * k + 1;
  loop invariant z == 6*n + 6;
  loop invariant z == 6 * n + 6;
  loop invariant y == 3*n*n + 3*n + 1;
  loop invariant y == 3 * n * n + 3 * n + 1;
  loop invariant x == n*n*n;
  loop invariant x == n * n * n;
  loop invariant n <= a + 1;
  loop invariant n - 1 <= a;
  loop invariant 0 <= n;
  loop invariant 0 <= a;
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns n;
  */
  while(n<=a){
       n=n+1;
       x=x+y;
       y=y+z;
       z=z+6;
  }
  // @ assert (n==a+1) && (y == 3*n*n + 3*n + 1) && (x == n*n*n) && (z == 6*n + 6);*/
}
