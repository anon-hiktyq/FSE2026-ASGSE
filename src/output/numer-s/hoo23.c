
/*@
    requires a > 0;
    requires b > 0;
    assigns \nothing;
    ensures \result == a * b;
    logic int a; // Declare a as a logic variable
    logic int b; // Declare b as a logic variable
*/
int hoo23() 
{
    int product = 0; 
    int i = 0;

    /*@
      loop invariant 0 <= i <= b;
      loop invariant product == a * i;
      loop assigns product, i;
    */
    while (i < b) {
        product = product + a;  
        i = i + 1;
    }

    /*@ assert product * product == (a * b) * (a * b); */
}
