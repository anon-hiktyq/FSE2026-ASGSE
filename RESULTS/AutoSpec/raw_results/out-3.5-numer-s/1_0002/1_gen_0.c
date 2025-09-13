//svcomp_css2003
int unknown();
/*@
  requires k >= 0;
  requires k <= 1;
*/
void hoo1(int k){
    int i = 1;
    int j = 1;

    //pre-condition
 

    //loop-body
    /*@
    Looking at this code, I need to analyze the loop behavior and the post-condition `i + k <= 2`.
    
    Initial values: `i = 1`, `j = 1`, `k` is between 0 and 1
    In each iteration: `i` increases by 1, `j` increases by `k`, `k` decreases by 1
    Post-condition: `i + k <= 2`
    
    ```c
    loop invariant i + k == 2;
    loop invariant i >= 1;
    loop invariant k <= 1;
    loop assigns i;
    loop assigns j; 
    loop assigns k;
    ```
    */
    while (unknown()) {
        i = i + 1;
        j = j + k;
        k = k - 1;
    }

    //post-condition
    /*@ assert i + k <= 2; */
}