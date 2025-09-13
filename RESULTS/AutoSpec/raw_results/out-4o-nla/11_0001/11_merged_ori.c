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
    loop invariant z * x - x + a - a * z * y == 0;
    loop invariant y == z^(c-1);
    loop invariant y == z^(c - 1);
    loop invariant y == \power(z, c - 1);
    loop invariant y == \pow(z, c - 1);
    loop invariant x == a * y + a * z * (\sum integer i; 0 <= i < c-1 ==> z^i);
    loop invariant x == a * y + a * (z * (1 - y)) / (z - 1);
    loop invariant x == a * (z^c - 1) / (z - 1);
    loop invariant x == a * (z^(c-1)) + a * (z^(c-2)) + ... + a;
    loop invariant x == a * (\power(z, c)) - a * (\power(z, c - 1));
    loop invariant x == a * (\pow(z, c) - 1) / (z - 1);
    loop invariant k > 0 && k <= 10;
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
  