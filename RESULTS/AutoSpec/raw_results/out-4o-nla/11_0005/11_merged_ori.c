/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/
int main11(int z,int k,int a){
  

    int x=a;
    int y=1;
    int c=1;
  
    /*@
    loop invariant z*x - x + a - a*z*y == 0;
    loop invariant z >= 0 && z <= 10;
    loop invariant z >= 0 && z <= 10 && k > 0 && k <= 10;
    loop invariant z * x - x + a - a * z * y == 0; // Maintains the assertion invariant dynamically within the loop.;
    loop invariant z * x - x + a - a * z * y == 0;
    loop invariant y == z^(c-1);
    loop invariant y == z^(c - 1); // y accumulates powers of z based on iteration.;
    loop invariant y == z^(c - 1);
    loop invariant x == a * y + a * z^(c-1);
    loop invariant x == a * y + a * z * (z^(c-1) - 1) / (z - 1); /* Arithmetic progression sum formula */;
    loop invariant x == a * y + a * z * (y - 1) / (z - 1);
    loop invariant x == a * y + a * (z^(c-1) - 1) / (z - 1);
    loop invariant x == a * y + (z * (x - a)) / z;
    loop invariant x == a * y + (y * (z - 1)) / (z - 1); // Expression derived from recursive relationship between x, y, and z.;
    loop invariant x == a * (z^(c-1)) + a * (z^(c-2)) + ... + a * (z^0);
    loop invariant x == a * (\sum integer i; 0 <= i < c; z^i);
    loop invariant k > 0 && k <= 10;
    loop invariant k - c;
    loop invariant c <= k;
    loop invariant 1 <= c;
    loop assigns y;
    loop assigns x;
    loop assigns c;
    */
    while (c < k){
   c = c + 1;
   x = x*z + a;
   y = y*z;
    }
  
  // @ assert z*x-x+a-a*z*y == 0;
  }
  