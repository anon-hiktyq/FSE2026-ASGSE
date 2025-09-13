/*@
requires z>=0 && z<=10 && k>0 && k<=10;
*/
void main11(int z,int k,int a){
  

    int x=a;
    int y=1;
    int c=1;
  
    /*@
    loop invariant 1 <= c <= k;
    loop invariant x == a * ((z^(c-1) - 1) / (z - 1)) + a; // When z != 1
    loop invariant y == z^(c-1); // For z^n representation
    loop invariant z >= 0 && z <= 10;
    loop invariant k > 0 && k <= 10;
    loop assigns c, x, y;
    */
    while (c < k){
   c = c + 1;
   x = x*z + a;
   y = y*z;
    }
  
  // @ assert z*x-x+a-a*z*y == 0;
  }
  