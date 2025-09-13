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
    loop invariant x == a * (z^(c-1)) + a * z^(c-2) + ... + a * z^0; // expanded polynomial form;
    loop invariant x == a * (z^(c-1)) + a * (z^(c-2)) + ... + a; // Geometric sum;
    loop invariant x == a * (z^(c-1)) + a * (z^(c-2)) + ... + a;
    loop invariant x == a * (z^(c-1)) + a * (z^(c-2)) + ... + a * z + a;
    loop invariant x == a * (z^(c-1)) + a * (z^(c-2)) + ... + a * (z^0);
    loop invariant x == a * (z^(c-1) + z^(c-2) + ... + z + 1); // Represents the polynomial expansion;
    loop invariant x == a * (z^(c - 1)) + a * (z^(c - 2)) + ... + a;
    loop invariant x == a * ((z^(c-1) - 1) / (z - 1)) * (z != 1) + c * a * (z == 1);
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
  