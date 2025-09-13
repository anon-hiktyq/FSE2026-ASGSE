
/*@
requires A >= 0 && B >= 1;
*/
void main12(int A,int B){
    
   
    int q = 0;
    int r = 0;
    int t = A;
   
    
    /*@
    loop invariant t >= 0;
    loop invariant q * B + r == A - t;
    loop invariant r >= 0 && r < B;
    loop invariant t + r == A - q * B;
    loop invariant r == (A - t) % B;
    loop invariant t <= A;
    loop invariant A == q * B + r + t;
    loop invariant q >= 0 && t >= 0;
    loop invariant t <= A;
    loop invariant t + r < A + B;
    loop invariant r >= 0 && r < B;
    loop invariant r == (A - t) % B;
    loop invariant r < B;
    loop invariant q * B + r == A - t;
    loop invariant q * B + r + t == A;
    loop invariant A >= 0 && B >= 1;
    loop invariant A == q * B + r + t;
    loop invariant 0 <= t;
    loop invariant 0 <= r;
    loop invariant 0 <= q;
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