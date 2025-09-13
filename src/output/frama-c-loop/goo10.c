
int mul10(int a, int b) {
    int x = a, y = b, prod = 0;

    /*@
      requires a >= 0; // Ensure a is non-negative for meaningful multiplication
      requires b >= 0; // Ensure b is non-negative for meaningful multiplication
      assigns prod; // Variables modified in the loop
      ensures prod == a * b; // Postcondition: prod should be the product of a and b

      loop invariant x >= 0; // x should be non-negative during the loop
      loop invariant prod == y * (a - x); // Correct invariant reflecting the product
      loop invariant y == b; // y is constant and equals b
      loop assigns prod; // Only prod is assigned in the loop
      loop variant x; // x is the variant that decreases
    */
    while(x >= 0) {
        prod = prod + y;
        x--;
    }
    
    return prod;
}

int goo10() {
    int pdt = mul10(2, 5);
    //@ assert pdt == 10;
}
