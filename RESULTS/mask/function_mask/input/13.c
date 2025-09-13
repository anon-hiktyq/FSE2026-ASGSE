void div_rem(unsigned x, unsigned y, unsigned* q, unsigned* r) {
    *q = x / y;
    *r = x % y;
}

// write a test
void goo13() {
    unsigned q, r;
    div_rem(10, 3, &q, &r);
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
   
}