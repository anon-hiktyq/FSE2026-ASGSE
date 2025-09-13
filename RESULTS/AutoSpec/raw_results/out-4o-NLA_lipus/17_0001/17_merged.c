/*@
requires k>=0 && k<=30;
*/
void main17(int k){
   
    int y=0;
    int x=0;
    int c=0;


    // loop body
    /*@
    loop invariant y == c;
    loop invariant c <= k;
    loop invariant 4*x - c*c*c*c - 2*(c*c*c) - (c*c) == 0;
    loop invariant 4*x - (c*c*c*c) - 2*(c*c*c) - (c*c) == 0;
    loop invariant 4 * x - (c * c * c * c) - 2 * (c * c * c) - (c * c) == 0;
    loop invariant 0 <= c;
    loop assigns y;
    loop assigns x;
    loop assigns c;
    */
    while(c < k){
     c = c +1 ;
     y = y +1;
     x=y*y*y+x;
    }
    //@ assert 4*x-(k*k*k*k)-2*(k*k*k)-(k*k) == 0;
}

