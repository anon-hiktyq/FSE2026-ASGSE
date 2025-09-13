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
    loop invariant s == \sum{0 <= i < a}; (2*i + 1);
    loop invariant t == 2*a + 1;
    loop invariant s == \sum{0 <= i < a+1}; (2*i + 1);
    loop invariant s == a*a;
    loop assigns a;
    loop assigns s;
    loop assigns t;
    */
    while(s <= n){
     a=a+1;
     t=t+2;
     s=s+t;
    }

    // post-condition
    //@ assert( n < (a + 1) * (a + 1));
}