
/*@
    requires A >= 0 && B >= 1;
    */
    
int main12(int A,int B){
    
    int q = 0;
    int r = 0;
    int t = A;
   
    /* >>> LOOP INVARIANT TO FILL <<< */
        
    /*@
        loop invariant (\at(A,Pre) != 0) ==> (q * B + r + t == A);
        loop invariant (\at(A,Pre) != 0) ==> (((t == \at(A,Pre)) && (r == 0) && (q == 0) && (B == \at(B,Pre)) && (A == \at(A,Pre))) || (0 <= r < B));
        loop invariant (\at(A,Pre) != 0) ==> (0 <= t <= \at(A,Pre));
        loop invariant (!(\at(A,Pre) != 0)) ==> ((t == \at(A,Pre)) && (r == 0) && (q == 0) && (B == \at(B,Pre)) && (A == \at(A,Pre)));
        loop invariant B == \at(B,Pre);
        loop invariant A == \at(A,Pre);
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
            
    /*@ assert q == A / B; */
}
