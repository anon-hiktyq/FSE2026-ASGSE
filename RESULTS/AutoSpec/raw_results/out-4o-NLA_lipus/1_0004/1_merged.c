/*@ requires a>=n && n==0;*/
void main1(int a,int n){
 
  int x,y,z;
  
  x=0;
  y=1;
  z=6;
  

  /*@
  loop invariant z == 6*(n-1) + 6 + 6;
  loop invariant z % 6 == 0;
  loop invariant y == 3*(n-1)*(n-1) + 3*(n-1) + 1 + (z - 6);
  loop invariant y == 3 * n * (n - 1) * (n - 1) / 2 + 3 * n + 1;
  loop invariant y == (n * (n - 1)) / 2 + 1;
  loop invariant y == (3 * n * (n - 1) / 2) + 1;
  loop invariant y <= z;
  loop invariant x == n * (n - 1) * (n - 2) / 6 + (y - 1) * (n - 1) + x;
  loop invariant x == (n * n * n) && y == (3 * n * n + 3 * n + 1) && z == (6 * n + 6);
  loop invariant x == (n * (n - 1) * (n - 2)) / 6;
  loop invariant x == (n * (n - 1) * (n - 2)) / 6 + n * y / 2 + x - 1;
  loop invariant x == (n * (n - 1) * (n - 1)) / 2;
  loop invariant x <= y;
  loop invariant n <= a;
  loop invariant n * n + n <= x;
  loop invariant a < n + 1;
  loop invariant \forall integer k; 0 <= k <= n ==> y == (3 * k * (k - 1)) / 2 + 1;
  loop invariant \forall integer k; 0 <= k <= n ==> x == k * y / 2 + (k * (k - 1) * (k - 2)) / 6;
  loop invariant 6 <= z;
  loop invariant 6 * (n + 1) <= z;
  loop invariant 1 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= a;
  loop invariant 0 < z;
  loop invariant 0 < y;
  loop invariant z == 6*n + 6;
  loop invariant z == 6 * n + 6;
  loop invariant y == 3*n*n + 3*n + 1;
  loop invariant y == 3 * n * n + 3 * n + 1;
  loop invariant x == n*n*n;
  loop invariant x == n * n * n;
  loop invariant n <= a+1;
  loop invariant n <= a + 1;
  loop invariant 0 <= n;
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
