/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

void main10(int z,int k){

    int x=1;
    int y=1;
    int c=1;
  
    /*@
    loop invariant y == z^(c-1);
    loop invariant y == z * (y/z);
    loop invariant y == z * (c-1) + 1;
    loop invariant y <= x;
    loop invariant x*z - x - z*y == 0;
    loop invariant x == z*y + 1;
    loop invariant x == z*(y + c) + 1;
    loop invariant x == y + c;
    loop invariant x == y + c * (z - 1) + 1;
    loop invariant x == c * z + 1;
    loop invariant x == 1 + z * y;
    loop invariant c <= k;
    loop invariant 1 <= y;
    loop invariant 1 <= x;
    loop invariant 1 <= c;
    loop invariant 1 + x * z - x - z * y == 0;;
    loop invariant 0 <= c;
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
  