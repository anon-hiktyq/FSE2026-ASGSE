
void foo19(int y) {
    int x = 1;

    /* >>> LOOP INVARIANT TO FILL <<< */
        
    /*@
      loop invariant 1 <= x <= 11;
      loop variant 11 - x; // Decreasing variant to ensure termination.
    */
    while (x <= 10) {
        y = 10 - x;
        x = x + 1;
    }

    /* mask_1 */
}
