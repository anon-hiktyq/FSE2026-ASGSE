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
    loop invariant 0 <= i <= b;
    loop invariant product == a * i;
    loop invariant a > 0;
    loop invariant b > 0;
    loop assigns i;
    loop assigns product;
    */
    while (i < b) {
        product = product + a;  
        i = i + 1;
    }

    
    
    /*@ assert product * product == (a * b) * (a * b); */
}