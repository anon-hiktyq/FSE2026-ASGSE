/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

int main10(int z,int k){

    int x=1;
    int y=1;
    int c=1;
  
    /*@
    loop invariant y == z^(c - 1); // (Exponential formula for y);
    loop invariant y == z^(c - 1);      // Geometric progression for y;
    loop invariant y == z^(c - 1);
    loop invariant y == (z^(c-1)); // z raised to the power (c-1);
    loop invariant x == (z^c - 1)/(z - 1); // (Geometric series formula for x);
    loop invariant x == (z^c - 1)/(z - 1);
    loop invariant x == (z^c - 1) / (z - 1); // Geometric progression for x;
    loop invariant x == (z^c - 1) / (z - 1);
    loop invariant x == (z^c - 1) / (z - 1) + 1;
    loop invariant x == (z^(c-1)) + (z^(c-2)) + ... + z + 1; // Summation of powers of z;
    loop invariant c <= k;
    loop invariant 1 <= c;
    loop invariant 1 + x*z - x - z*y == 0;  // Maintains the relationship between x and y;
    loop invariant 1 + x*z - x - z*y == 0;
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
  