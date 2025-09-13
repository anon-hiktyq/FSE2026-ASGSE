/*@ requires x>0;
    requires y>0;
*/
int main3(int x,int y){
 
    int q=0;
    int r=0;
    
    /*@
    loop invariant y * q < x;
    loop invariant y * q + r; < x;
    loop invariant y * q + r <= x;
    loop invariant y * q + r < x;
    loop invariant y * q + r - 1 < x;
    loop invariant x == y * q + r + (y * (q - 1) + r + 1);
    loop invariant x == (y * q) + r + 1;
    loop invariant r < y;;
    loop invariant r < y;
    loop invariant r < x;
    loop invariant q <= x / y;
    loop invariant q * y + r <= x;
    loop invariant 0 <= r;
    loop invariant 0 <= q;
    loop invariant 0 < y;
    loop invariant 0 < x;
    loop invariant 0 < x - y * q - r;
    loop assigns r;
    loop assigns q;
    */
    while(x > y * q + r) {
        if (r == y - 1){
            r = 0;
            q += 1;
        }
        else{
            r += 1;
        }
  
    }
    //@ assert(x == q*y+r);
  }
  
