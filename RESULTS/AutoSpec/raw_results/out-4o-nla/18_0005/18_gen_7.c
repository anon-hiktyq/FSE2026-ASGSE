/*@
requires k>=0 && k<=30;
*/
int main18(int k){
   
    int y=0;
    int x=0;
    int c=0;

    // loop body
    /*@
    loop invariant 0 <= c <= k;
    loop invariant y == c;
    loop invariant x == y*y*y*y*c - c + (y*y*y*y-1)*(c-1)/6;
    loop invariant x >= 0;
    loop assigns c, y, x;
    */
    while(c < k){
     c = c +1 ;
     y = y +1;
     x = y*y*y*y+x;
    }

    // @ assert 6*k*k*k*k*k + 15*k*k*k*k+ 10*k*k*k - 30*x - k == 0;
}
