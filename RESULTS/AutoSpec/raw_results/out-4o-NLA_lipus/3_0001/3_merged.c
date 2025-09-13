/*@ requires x>0;
    requires y>0;
*/
void main3(int x,int y){
 
    int q=0;
    int r=0;
    
    /*@
    loop invariant y * q + r - 1 < x;
    loop invariant x > 0 && y > 0;
    loop invariant x == q * y + r + (x - (y * q + r));
    loop invariant r < y;
    loop invariant q <= x / y;
    loop invariant q * y + r <= x;
    loop invariant 0 <= r;
    loop invariant 0 <= q;
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
  
