/*@
requires k>=0 && k<=30;
*/
void main19(int k){
   
    int y=0;
    int x=0;
    int c=0;

    // loop body
    /*@
    loop invariant y*y*y*y*y <= x;
    loop invariant y <= k;
    loop invariant y <= c;
    loop invariant x == y*y*y*y*y;
    loop invariant x == y*y*y*y*y*y - y*y*y*y*y;
    loop invariant x == y*y*y*y*y*y - y*y*y*y*y - y*y*y*y + y*y;
    loop invariant x == y*y*y*y*y*c;
    loop invariant x == y*y*y*y*y*c / (c + 1);
    loop invariant x == y*y*y*y*y*(c) / c;
    loop invariant c == y;
    loop invariant \forall integer n; 0 <= n <= k ==> y == n ==> c == n;
    loop invariant \forall integer n; 0 <= n <= k ==> x == y*y*y*y*y*y;
    loop invariant \forall integer n; 0 <= n < c ==> n <= k;
    loop invariant \forall integer m; 0 <= m < c ==> m <= k;
    loop invariant \forall integer j; 0 <= j < c ==> x >= 0;
    loop invariant \forall integer i; 0 <= i < c ==> y == i;
    loop invariant \forall integer i; 0 <= i < c ==> x == y*y*y*y*y;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
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