/*@
requires k>=0 && k<=30;
*/
void main19(int k){
   
    int y=0;
    int x=0;
    int c=0;

    // loop body
    /*@
    loop invariant y == c;
    loop invariant x == \sum(0, c-1, \lambda integer j; (j+1)*(j+1)*(j+1)*(j+1)*(j+1));
    loop invariant c <= k;
    loop invariant 0 <= c;
    loop invariant -2*(c*c*c*c*c*c) - 6*(c*c*c*c*c) - 5*(c*c*c*c) + (c*c) + 12*x == 0;
    loop assigns y;
    loop assigns x;
    loop assigns c;
    */
    while(c < k){
     c = c + 1 ;
     y = y + 1;
     x=y*y*y*y*y+x;
    }

    // @ assert -2*(k*k*k*k*k*k) - 6*(k*k*k*k*k) - 5*(k*k*k*k) + (k*k) + 12*x == 0;

}