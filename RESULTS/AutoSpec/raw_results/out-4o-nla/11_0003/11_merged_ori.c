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
    loop invariant z > 0 && z <= 10;
    loop invariant z * x - x + a - a * z * y == 0;
    loop invariant y == z^(c-1);
    loop invariant y == z^(c - 1);;
    loop invariant y == z^(c - 1);
    loop invariant y == \power(z, c);
    loop invariant y == \pow(z, c - 1);
    loop invariant x == a * y + a * z * (z^(c - 1) - 1) / (z - 1);
    loop invariant x == a * y + a * (z^(c-1) - 1) / (z - 1);
    loop invariant x == a * y + a * (z * (y - 1)) / (z - 1);
    loop invariant x == a * (z^c - 1) / (z - 1);
    loop invariant x == a * (z^(c-1)) + a * (z^(c-2)) + ... + a;
    loop invariant x == a * (z^(c-1)) + a * (z^(c-2)) + ... + a * z + a;
    loop invariant x == a * (\power(z, c)) - a;
    loop invariant x == a * (\pow(z, c) - 1) / (z - 1); /* Geometric sum formula */;
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
  