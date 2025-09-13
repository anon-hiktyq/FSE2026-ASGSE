//svcomp_benchmark47_linear
int unknown();
/*@
  requires x < y;
  requires y <= 20000001;
*/
void hoo17(int x,int y){
    

    //pre-condition
    //loop-body
    /*@
    Looking at this loop, I need to analyze what happens to `x` and `y` in each iteration and find invariants that hold throughout the loop execution.
    
    The loop continues while `x < y`, and in each iteration:
    - If `x < 0`, then `x += 7`, otherwise `x += 10`
    - If `y < 0`, then `y -= 10`, otherwise `y += 3`
    
    The key insight is that the loop will eventually terminate and we need to maintain relationships that ensure the post-condition `x <= y + 16` holds.
    
    ```c
    loop invariant x <= y + 16;
    loop assigns x;
    loop assigns y;
    ```
    */
    while (x < y) {
        if (x < 0){
            x = x + 7; 
        }
        else {
            x = x + 10;
        }
        if (y < 0){
            y = y - 10;
        } 
        else {
            y = y + 3;
        }

    }

    //post-condition
    /*@ assert x <= y + 16; */
}