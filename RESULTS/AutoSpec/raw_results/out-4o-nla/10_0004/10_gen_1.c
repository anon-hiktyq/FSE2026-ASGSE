/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

int main10(int z,int k){

    int x=1;
    int y=1;
    int c=1;
  
    /*@
    loop invariant 1 <= c <= k;
    loop invariant x == (z * x_prev) + 1; // `x_prev` is the value of x from the previous iteration
    loop invariant y == pow(z, c - 1); // Tracks the power relationship between `y` and `z`
    loop invariant 1 + x * z - x - z * y == 0;
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
  