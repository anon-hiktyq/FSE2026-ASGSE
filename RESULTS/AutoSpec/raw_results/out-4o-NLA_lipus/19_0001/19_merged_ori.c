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
    loop invariant x == y^5 + (y-1)^5 + ... + 1^5;
    loop invariant x == \sum{integer j; 0 <= j < c; j^5};
    loop invariant x == \sum{0 <= i < c} i*i*i*i*i;
    loop invariant x == \sum_{j=1}^c j^5;
    loop invariant x == \sum_{i=1}^{c} i^5;
    loop invariant x == \sum(1 <= i <= c, i^5);
    loop invariant x == (\sum integer j; 0 <= j < c; j^5);
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