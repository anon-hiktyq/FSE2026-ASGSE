/*@ requires x>0;
    requires y>0;
*/
int main4(int x,int y){
 
    int q=0;
    int r=0;
    
    /*@
    loop invariant y * q <= x;
    loop invariant y * q + r <= x;
    loop invariant r >= 0 && r < y;
    loop invariant r < y;
    loop invariant q*y + r <= x;
    loop invariant q * y + r <= x;
    loop invariant 0 <= r;
    loop invariant 0 <= q;
    loop invariant 0 < y;
    loop invariant 0 < x;
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
