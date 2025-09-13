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
    loop invariant product == i * a;
    loop invariant i <= b;
    loop invariant 0 <= i;
    loop assigns product;
    loop assigns i;
    ```c;
    ```;
    Looking at this multiplication-by-addition algorithm, I need to establish invariants that track the relationship between the loop counter, the accumulating product, and the final assertion.;
    */
    while (i < b) {
        product = product + a;  
        i = i + 1;
    }

    
    
    /*@ assert product * product == (a * b) * (a * b); */
}