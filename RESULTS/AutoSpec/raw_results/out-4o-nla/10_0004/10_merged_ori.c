/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

int main10(int z,int k){

    int x=1;
    int y=1;
    int c=1;
  
    /*@
    loop invariant z >= 0 && z <= 10 && k > 0 && k <= 10;
    loop invariant y == z^c;
    loop invariant y == z^(c-1); // Exponential representation for y;
    loop invariant y == z^(c - 1);
    loop invariant y == z ^ (c - 1);
    loop invariant y == pow(z, c - 1); // Tracks the power relationship between `y` and `z`;
    loop invariant y == \pow(z, c - 1);
    loop invariant x == z * y + 1;
    loop invariant x == y + c;
    loop invariant x == 1 + z * (y - 1);
    loop invariant x == (z^c - 1) / (z - 1);
    loop invariant x == (z^(c-1)) + (z^(c-2)) + ... + 1; // Summation representation for x;
    loop invariant x == (z*c - z + 1);
    loop invariant x == (z * x_prev) + 1; // `x_prev` is the value of x from the previous iteration;
    loop invariant x == (z * x + 1) / z;
    loop invariant c <= k;
    loop invariant 1 <= y;
    loop invariant 1 <= x;
    loop invariant 1 <= c;
    loop invariant 1 + x*z - x - z*y == 0;
    loop invariant 1 + x * z - x - z * y == 0;
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
  