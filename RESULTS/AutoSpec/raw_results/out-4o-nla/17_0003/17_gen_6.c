/*@
requires k>=0 && k<=30;
*/
int main17(int k){
   
    int y=0;
    int x=0;
    int c=0;


    // loop body
    /*@
    loop invariant 0 <= c <= k;
    loop invariant y == c;
    loop invariant x == y*y*y*(c - 1) / 3 + y*y * (c - 1) * (c - 2) / 6 + y * (c - 1);
    loop invariant 4*x == c*c*c*c + 2*c*c*c + c*c;
    loop assigns c, x, y;
    */
    while(c < k){
     c = c +1 ;
     y = y +1;
     x=y*y*y+x;
    }
    // @ assert 4*x-(k*k*k*k)-2*(k*k*k)-(k*k) == 0;
}

