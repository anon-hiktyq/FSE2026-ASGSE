
void goo4(){
    int i = 0;

    /*@
      loop invariant 0 <= i <= 30;
      loop invariant \forall integer k; 0 <= k <= i ==> k <= 30;
      loop assigns i;
    */
    while (i < 30){
        ++i;
    }
    /* MASK_ACSL_ASSERT */
}
