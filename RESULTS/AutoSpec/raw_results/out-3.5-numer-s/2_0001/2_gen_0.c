//svcomp_bin-suffix-5
int unknown();
void hoo2(){
    //pre-condiiton
    int x =5;
   
    //loop-body
    /*@
    Looking at this code, I need to generate a loop invariant for the while loop that maintains the property needed for the post-condition assertion.
    
    The key insight is that `x` starts at 5, and in each iteration we add 8 to `x`. Since we're adding multiples of 8, the remainder when dividing by 8 will always stay the same (5).
    
    ```c
    loop invariant (x % 8) == 5;
    loop assigns x;
    ```
    */
    while(unknown()){
        x = x + 8;
    }

    //post-condition
    /*@ assert (x % 8) == 5; */
}