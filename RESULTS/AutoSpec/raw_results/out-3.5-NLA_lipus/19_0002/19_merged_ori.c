/*@
requires k>=0 && k<=30;
*/
void main19(int k){
   
    int y=0;
    int x=0;
    int c=0;

    // loop body
    /*@
    loop invariant x == (y*(y+1)*(2*y+1)*(3*y*y+3*y-1))/30;
    loop invariant c == y;
    loop invariant \exists integer j; 0 <= j <= y && x == j*(j+1)*(2*j+1)*(3*j*j+3*j-1)/30;
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