/*@
  requires a > 0;
  requires b > 0;
*/
void hoo23() 
{
    
    int a, b;
    int product = 0; 
    int i = 0;


    
    /*@
    Looking at this multiplication-by-addition algorithm, I need to establish invariants that track the relationship between the loop counter, the accumulating product, and the final assertion.
    
    ```c
    loop invariant 0 <= i <= b;
    loop invariant product == i * a;
    loop assigns product, i;
    ```
    */
    while (i < b) {
        product = product + a;  
        i = i + 1;
    }

    
    
    /*@ assert product * product == (a * b) * (a * b); */
}