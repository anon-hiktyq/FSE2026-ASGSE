/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/
int main11(int z,int k,int a){
  

    int x=a;
    int y=1;
    int c=1;
  
    /*@
    loop invariant 1 <= c <= k;
    loop invariant x == a * y + (y * (z - 1)) / (z - 1);  // Expression derived from recursive relationship between x, y, and z.
    loop invariant y == z^(c - 1);  // y accumulates powers of z based on iteration.
    loop invariant z * x - x + a - a * z * y == 0;  // Maintains the assertion invariant dynamically within the loop.
    loop assigns c, x, y;
    loop variant k - c;
    */
    while (c < k){
   c = c + 1;
   x = x*z + a;
   y = y*z;
    }
  
  // @ assert z*x-x+a-a*z*y == 0;
  }
  