/*@ requires x>0;
    requires y>0;
*/
void main4(int x,int y){
 
    int q=0;
    int r=0;
    
    /*@
    Looking at this division algorithm, I need to identify the loop invariants that maintain the relationship between the variables throughout the loop execution.
    
    ```c
    loop invariant q >= 0;
    loop invariant 0 <= r < y;
    loop invariant x == q*y + r + (x - q*y - r);
    loop invariant q*y + r <= x;
    loop assigns q;
    loop assigns r;
    ```
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
