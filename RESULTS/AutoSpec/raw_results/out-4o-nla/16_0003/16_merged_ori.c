/*@
requires k >= 0 && k <= 30;
*/
int main16(int k){
   
    int y=0;
    int x=0;
    int c=0;


    // loop body
    /*@
    loop invariant y == c;
    loop invariant x == y*y*(y+1)/3;
    loop invariant x == y * (y - 1) * (2 * y - 1) / 6;
    loop invariant x == y * (y * y + 1) / 2;
    loop invariant x == c * c * (c + 1) / 2;
    loop invariant x == c * (c + 1) * (2 * c + 1) / 6;
    loop invariant x == \sum{integer j; 0 <= j < c; (j+1)*(j+1)};
    loop invariant x == (\sum integer i; 1 <= i <= c; i*i);
    loop invariant c <= k;
    loop invariant 6*x == 2*c*c*c + 3*c*c + c;
    loop invariant 6*x - 2*c*c*c - 3*c*c - c == 0;
    loop invariant 0 <= c;
    loop assigns y;
    loop assigns x;
    loop assigns c;
    */
    while(c < k){
     c = c + 1;
     y = y + 1;
     x = y * y + x;
    }
    // @ assert 6*x-2*k*k*k-3*k*k-k == 0;
}
