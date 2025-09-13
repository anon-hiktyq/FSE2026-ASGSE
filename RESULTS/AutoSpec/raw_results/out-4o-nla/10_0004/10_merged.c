/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/

int main10(int z,int k){

    int x=1;
    int y=1;
    int c=1;
  
    /*@
    loop invariant z >= 0 && z <= 10 && k > 0 && k <= 10;
    loop invariant y == \pow(z, c - 1);
    loop invariant x == 1 + z * (y - 1);
    loop invariant x == (z^c - 1) / (z - 1);
    loop invariant x == (z*c - z + 1);
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
  
  }
  