/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

int main10(int z,int k){

    int x=1;
    int y=1;
    int c=1;
  
    /*@
    loop invariant 1 <= c <= k;
    loop invariant x == (z^c - 1)/(z - 1); // Geometric series sum formula for x
    loop invariant y == z^(c - 1);         // Power of z for y
    loop invariant 1 + x * z - x - z * y == 0; // Maintains the given assertion
    loop assigns c, x, y;
    */
    while (c < k){
   c = c + 1;
   x = x*z + 1;
   y = y*z;
    }
  
   //@ 1+x*z-x-z*y==0;
  }
  