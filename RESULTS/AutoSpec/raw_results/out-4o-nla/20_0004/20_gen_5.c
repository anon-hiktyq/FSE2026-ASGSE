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
    loop invariant 0 <= s <= n + t;
    loop invariant t == 2 * a + 1;
    loop invariant s == a * (a + 1) + 1;
    loop invariant n < (a + 1) * (a + 1) || s <= n;
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