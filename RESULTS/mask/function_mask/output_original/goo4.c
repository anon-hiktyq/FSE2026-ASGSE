
void goo4(){
    int i = 0;

    /*@
      requires \true;
      ensures i == 30;
    */
    /*@
      loop invariant 0 <= i <= 30;
      loop invariant \forall integer k; 0 <= k <= i ==> k <= 30;
      loop assigns i;
      loop variant 30 - i;
    */
    while (i < 30){
        ++i;
    }
    /* MASK_ACSL_ASSERT */
}
