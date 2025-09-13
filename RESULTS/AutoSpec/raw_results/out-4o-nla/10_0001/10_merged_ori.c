/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

int main10(int z,int k){

    int x=1;
    int y=1;
    int c=1;
  
    /*@
    loop invariant z >= 0 && z <= 10;
    loop invariant y == z^(c-1);
    loop invariant y == z^(c - 1);     // Power of z for y;
    loop invariant y == z^(c - 1);
    loop invariant y == \pow(z, c - 1);
    loop invariant x == (z^c - 1)/(z - 1); // Geometric series sum formula for x;
    loop invariant x == (z^c - 1) / (z - 1);
    loop invariant x == (z^c - 1) / (z - 1) + 1;
    loop invariant x == (z^(c-1)) + (z^(c-2)) + ... + z + 1; // (geometric series sum);
    loop invariant x == (z^(c-1)) + (z^(c-2)) + ... + z + 1;
    loop invariant x == (y * z) + 1;
    loop invariant k > 0 && k <= 10;
    loop invariant c <= k;
    loop invariant 1 <= c;
    loop invariant 1 + x*z - x - z*y == 0;
    loop invariant 1 + x * z - x - z * y == 0; // Maintains the given assertion;
    loop invariant 1 + x * z - x - z * y == 0;
    loop assigns y;
    loop assigns x;
    loop assigns c;
    ```c;
    ```;
    */
    while (c < k){
   c = c + 1;
   x = x*z + 1;
   y = y*z;
    }
  
   //@ 1+x*z-x-z*y==0;
  }
  