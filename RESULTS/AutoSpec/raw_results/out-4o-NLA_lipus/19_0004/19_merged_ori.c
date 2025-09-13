/*@
requires k>=0 && k<=30;
*/
void main19(int k){
   
    int y=0;
    int x=0;
    int c=0;

    // loop body
    /*@
    loop invariant y <= k;
    loop invariant y <= c;
    loop invariant x == y^5 * (c - y) + y^5 * (y - 1) * y / 2;
    loop invariant x == y*y*y*y*y*(c - y + 1);
    loop invariant x == y*y*y*y*y + \sum_{i=1}^{c-1}(i*i*i*i*i);
    loop invariant x == y*y*y*y*y + (y-1)*(y-1)*(y-1)*(y-1)*(y-1);
    loop invariant x == y*y*y*y*y * (c - y) / c;
    loop invariant x == y * y * y * y * y;
    loop invariant x == c * y*y*y*y*y;
    loop invariant x == (c*c*c*c*c)*y/5;
    loop invariant c == y;;
    loop invariant c == y;
    loop invariant c <= k && 0 <= y <= c;
    loop invariant \forall integer n; 0 <= n < c ==> y == n+1;
    loop invariant \forall integer i; 0 <= i < c ==> y == i + 1;
    loop invariant 0 <= y;
    loop invariant y == c;
    loop invariant c <= k;
    loop invariant 0 <= x;
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