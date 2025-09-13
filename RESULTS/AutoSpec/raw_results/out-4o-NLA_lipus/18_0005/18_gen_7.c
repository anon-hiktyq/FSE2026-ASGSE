/*@
requires k>=0 && k<=30;
*/
void main18(int k){
   
    int y=0;
    int x=0;
    int c=0;

    // loop body
    /*@
    loop invariant 0 <= c <= k;
    loop invariant y == c;
    loop invariant x == \sum(0, c-1, \lambda integer i; (i+1)*(i+1)*(i+1)*(i+1)) + 0;
    loop invariant x == \sum(1, c, \lambda integer i; i*i*i*i) + \sum(1, c, \lambda integer i; i*i*i*i);
    loop assigns c;
    loop assigns y;
    loop assigns x;
    */
    while(c < k){
     c = c +1 ;
     y = y +1;
     x = y*y*y*y+x;
    }

    // @ assert 6*k*k*k*k*k + 15*k*k*k*k+ 10*k*k*k - 30*x - k == 0;
}
