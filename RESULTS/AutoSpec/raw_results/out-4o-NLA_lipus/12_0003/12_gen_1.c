
/*@
requires A >= 0 && B >= 1;
*/
void main12(int A,int B){
    
   
    int q = 0;
    int r = 0;
    int t = A;
   
    
    /*@
    loop invariant A >= 0 && B >= 1;
    loop invariant t >= 0;
    loop invariant t == A - q * B - r;
    loop invariant q == (A - r) / B;
    loop invariant 0 <= r < B;
    loop invariant q >= 0;
    loop assigns q, r, t;
    */
    while(t != 0) {
     if (r + 1 == B) {
          q = q + 1;
          r = 0;
          t = t - 1;
     }
     else {
          r = r + 1;
          t = t - 1;
     }
    }
    // @ assert q == A / B;
}