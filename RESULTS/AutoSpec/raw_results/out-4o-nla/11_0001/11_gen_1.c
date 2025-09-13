/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/
int main11(int z,int k,int a){
  

    int x=a;
    int y=1;
    int c=1;
  
    /*@
    loop invariant 1 <= c <= k;
    loop invariant x == a * y + a * z * (\sum integer i; 0 <= i < c-1 ==> z^i);
    loop invariant y == z^(c-1);
    loop invariant z*x - x + a - a*z*y == 0;
    loop assigns c, x, y;
    */
    while (c < k){
   c = c + 1;
   x = x*z + a;
   y = y*z;
    }
  
  // @ assert z*x-x+a-a*z*y == 0;
  }
  