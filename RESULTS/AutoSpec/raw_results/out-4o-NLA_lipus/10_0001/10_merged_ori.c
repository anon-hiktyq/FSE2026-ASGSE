/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

void main10(int z,int k){

    int x=1;
    int y=1;
    int c=1;
  
    /*@
    loop invariant z >= 0 && z <= 10;
    loop invariant y == z^(c-1);
    loop invariant x == z^(c-1) + c;
    loop invariant x == y*z + c;
    loop invariant x == y + z * (c - 1) + 1;
    loop invariant x == y + c;;
    loop invariant x == y + c;
    loop invariant x == y + c - 1;
    loop invariant x == c*z + 1;
    loop invariant x == (z * y) + c;
    loop invariant c <= k;
    loop invariant \forall integer n; 0 <= n < c ==> x == n * z + 1 + y;
    loop invariant 1+x*z-x-z*y == 0;;
    loop invariant 1 <= y;
    loop invariant 1 <= x;
    loop invariant 1 <= c;
    loop invariant 1 + x*z - x - z*y == 0;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop assigns y;
    loop assigns x;
    loop assigns c;
    */
    while (c < k){
   c = c + 1;
   x = x*z + 1;
   y = y*z;
    }
  
   //@ 1+x*z-x-z*y==0;
  }
  