
/*@
 requires \valid(q) && \valid(r);
 requires \separated(q, r);
 requires y != 0;
 ensures *q == x / y && *r == x % y;
*/

void div_rem(unsigned x, unsigned y, unsigned* q, unsigned* r) 
{
    *q = x / y;
    *r = x % y;
}

void goo13() {
    unsigned q, r;
    div_rem(10, 3, &q, &r);
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
}
