/*@
  requires a >= 0;
  requires b >= 0;
*/
void hoo37(int a, int b) {
    
    int product = 0;  
    int i = 0;        

    
    /*@
    loop invariant 0 <= i <= b;
    loop invariant product == a * i;
    loop invariant product >= 0;
    loop assigns product;
    loop assigns i;
    */
    while (i < b) {
        product = product + a;  
        i = i + 1;
    }

    
    /*@ assert product == a * b; */
}