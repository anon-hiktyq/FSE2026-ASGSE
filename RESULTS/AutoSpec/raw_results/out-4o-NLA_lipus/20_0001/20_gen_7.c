/*@
requires n >= 0;
*/
void main20(int n){
    // variable declarations

    //precondition
    int a=0;
    int s=1;
    int t=1;

    // loop body
    /*@
    loop invariant 0 <= a;
    loop invariant 1 <= t;
    loop invariant 1 <= s;
    loop invariant s == 1 + t * (t - 1) / 2;
    loop invariant 2*a + 1 == t;
    loop invariant s <= n + 1;
    loop assigns a, s, t;
    */
    while(s <= n){
     a=a+1;
     t=t+2;
     s=s+t;
    }

    // post-condition
    //@ assert( n < (a + 1) * (a + 1));
}