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
    loop invariant product == a * i;
    loop invariant i <= b;
    loop invariant 0 <= i;
    loop assigns product;
    loop assigns i;
    ```c;
    ```;
    */
    while (i < b) {
        product = product + a;  
        i = i + 1;
    }

    
    
    /*@ assert product * product == (a * b) * (a * b); */
}