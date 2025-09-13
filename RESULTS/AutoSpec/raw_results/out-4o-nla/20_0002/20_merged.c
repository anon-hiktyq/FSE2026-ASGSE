/*@
requires n >= 0;
*/
int main20(int n){
    // variable declarations

    //precondition
    int a=0;
    int s=1;
    int t=1;

    // loop body
    /*@
    loop invariant t == 2*a + 1;
    loop invariant t == 2 * a + 1;
    loop invariant t == 1 + 2 * a;
    loop invariant s == a * a + 1;
    loop invariant s == 1 + a * (a + 1);
    loop invariant s == (a + 1) * (a + 2) / 2;
    loop invariant s == (a + 1) * (a + 1);
    loop invariant s <= n + t;
    loop invariant s <= n + 1;
    loop invariant a <= n;
    loop invariant 1 <= s;
    loop invariant 0 <= a;
    loop assigns t;
    loop assigns s;
    loop assigns a;
    */
    while(s <= n){
     a=a+1;
     t=t+2;
     s=s+t;
    }

    // post-condition
    //@ assert( n < (a + 1) * (a + 1));
}