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
    loop invariant x == y*y*y*y*y*y/6 + y*y*y*y*y/2 + y*y*y*y*5/12 - y*y*y*y/2 - y*y*y*y*5/12;
    loop invariant x == y*y*y*y*y*c;
    loop invariant x == y*y*y*y*y + \sum(0, c-1, \lambda integer j; j*j*j*j*j);
    loop invariant x == y*y*y*y*y + \sum(0, c-1, \lambda integer d; (d*d*d*d*d));
    loop invariant x == y*y*y*y*y + \sum(0 <= t < c; t*t*t*t*t);
    loop invariant x == c*c*c*c*c + x_old: (x == \old(x) + y*y*y*y*y*(c - c_old));
    loop invariant x == \sum(0 <= i < c, i^5);
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