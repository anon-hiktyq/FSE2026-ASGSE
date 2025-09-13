//svcomp_benchmark32_linear
int unknown();
/*@
  requires x == 1 || x == 2;
*/
void hoo13(int x){

    //loop-body
    /*@
    Looking at the loop in the `hoo13` function:
    
    ```c
    while (unknown()) {
        if(x == 1) 
            x = 2;
        else if(x == 2)
            x = 1;
    }
    ```
    
    The loop invariant should capture that `x` alternates between values 1 and 2, and never exceeds 8 (as required by the post-condition assertion).
    
    ```c
    loop invariant x == 1 || x == 2;
    loop assigns x;
    ```
    */
    while (unknown()) {
        if(x == 1) 
            x = 2;
        else if(x == 2)
            x = 1;
    }

    //post-condition
    /*@ assert x <= 8; */
}