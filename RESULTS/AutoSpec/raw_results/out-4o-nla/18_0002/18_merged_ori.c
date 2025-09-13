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
    loop invariant x == y*y*y*y*(y+1)/5 - y*(y+1)*(2*y+1)/6;
    loop invariant x == y*y*y*y + x - y*y*y*y;
    loop invariant x == \sum_{i=1}^{c} i^4;
    loop invariant x == \sum_{i=0}^{c-1} (i+1)^4;
    loop invariant x == \sum(0, c-1, \lambda integer i; (i+1)*(i+1)*(i+1)*(i+1));
    loop invariant c <= k;
    loop invariant 6*y^5 + 15*y^4 + 10*y^3 - 30*x - y == 0;
    loop invariant 6*c*c*c*c*c + 15*c*c*c*c + 10*c*c*c - 30*x - c == 0;
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
