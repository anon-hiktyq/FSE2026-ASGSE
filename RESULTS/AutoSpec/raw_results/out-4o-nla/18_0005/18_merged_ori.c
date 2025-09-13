/*@
requires k>=0 && k<=30;
*/
int main18(int k){
   
    int y=0;
    int x=0;
    int c=0;

    // loop body
    /*@
    loop invariant y == c;
    loop invariant x == y*y*y*y*y;
    loop invariant x == y*y*y*y*x + \sum(0, c-1, j, j*j*j*j);
    loop invariant x == y*y*y*y*c;
    loop invariant x == y*y*y*y*c - c + (y*y*y*y-1)*(c-1)/6;
    loop invariant x == c*c*c*c + x;
    loop invariant x == \sum_{i=0}^{c-1} (i^4);
    loop invariant x == \sum(0..c-1, \lambda integer i; (i+1)*(i+1)*(i+1)*(i+1));
    loop invariant x == \sum(0 <= j < c, j^4);
    loop invariant x == \sum(0 <= i < c, i*i*i*i);
    loop invariant c <= k;
    loop invariant 6*c*c*c*c*c + 15*c*c*c*c + 10*c*c*c - 30*x - c == 0;
    loop invariant 0 <= x;
    loop invariant 0 <= c;
    loop assigns y;
    loop assigns x;
    loop assigns c;
    */
    while(c < k){
     c = c +1 ;
     y = y +1;
     x = y*y*y*y+x;
    }

    // @ assert 6*k*k*k*k*k + 15*k*k*k*k+ 10*k*k*k - 30*x - k == 0;
}
