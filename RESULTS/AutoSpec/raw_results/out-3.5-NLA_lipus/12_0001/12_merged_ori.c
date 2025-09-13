
/*@
requires A >= 0 && B >= 1;
*/
void main12(int A,int B){
    
   
    int q = 0;
    int r = 0;
    int t = A;
   
    
    /*@
    loop invariant t <= A;
    loop invariant r < B;
    loop invariant A == q * B + r + t;
    loop invariant 0 <= t;
    loop invariant 0 <= r;
    loop assigns t;
    loop assigns r;
    loop assigns q;
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