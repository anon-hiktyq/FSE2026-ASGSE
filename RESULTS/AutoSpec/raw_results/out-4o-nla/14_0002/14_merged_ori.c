/*@
requires a >= 0 && b >= 0;
*/
int main14(int a,int b){
   
    int x=a;
    int y=b;
    int z=0;

    // loop body
    /*@
    loop invariant z == (original_y - y) * a + \floor(y / 2) * a * 2;
    loop invariant z + x * y == a * b;
    loop invariant z + x * y == a * \old(b);
    loop invariant y;
    loop invariant x == a * 2^(b - y);
    loop invariant x == a * 2^((\old(b) - y) / 2);
    loop invariant x == a * (1 << (\old(b) - b));
    loop invariant x == 2^(original_y - \floor(y)) * a;
    loop invariant \forall integer k; 0 <= k < b - y ==> ((b - k) % 2 == 1 ==> z + x * (b - k) == a * b);
    loop invariant \exists integer k; 0 <= k <= b && y == b - k;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop assigns z;
    loop assigns y;
    loop assigns x;
    */
    while(y!=0) {
     
     if (y%2 ==1 ){
          z = z+x;
          y = y-1;
     }
     x = 2*x;
     y = y/2;
    }

    // @ assert z == a*b;
}
