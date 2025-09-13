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
    loop invariant c <= k;
    loop invariant 0 <= c <= k;
    loop invariant x == (c*(c-1)*(2*c-1)*(3*c*c-3*c+1))/30;
    loop invariant \forall integer j; 0 <= j < c ==> y == j + 1;
    loop invariant x <= (k*k*k*k*k*k)*(c/k);
    loop invariant y == c;
    loop invariant c <= k;
    loop invariant 0 <= c;
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