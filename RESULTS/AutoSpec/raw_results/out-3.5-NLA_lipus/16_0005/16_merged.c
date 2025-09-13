/*@
requires k >= 0 && k <= 30;
*/
void main16(int k){
   
    int y=0;
    int x=0;
    int c=0;


    // loop body
    /*@
    loop invariant y == c;
    loop invariant c <= k;
    loop invariant 6*x == 2*c*c*c + 3*c*c + c;
    loop invariant 0 <= c;
    loop assigns y;
    loop assigns x;
    loop assigns c;
    */
    while(c < k){
     c = c + 1;
     y = y + 1;
     x = y * y + x;
    }
    //@ assert 6*x-2*k*k*k-3*k*k-k == 0;
}
