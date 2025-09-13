/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

void main10(int z,int k){

    int x=1;
    int y=1;
    int c=1;
  
    /*@
    loop invariant 1 <= c <= k;
    loop invariant x == y + c;
    loop invariant x == y + c;
    loop invariant x == y + c;
    loop invariant \forall integer n; 1 <= n <= c ==> x == y + n;
    loop invariant \forall integer n; 1 <= n <= c ==> x == y + n;
    loop assigns c;
    loop assigns x;
    loop assigns y;
    */
    while (c < k){
   c = c + 1;
   x = x*z + 1;
   y = y*z;
    }
  
   //@ 1+x*z-x-z*y==0;
  }
  