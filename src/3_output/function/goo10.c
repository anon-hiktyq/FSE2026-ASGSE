



/*@
 requires \valid(a) && \valid(b) ;
 requires \separated(a,b) ;

ensures *a == \old(*a) + \old(*b)&&*b == \old(*b);
ensures \result == \old(*a) + \old(*b);

*/

int incr_a_by_b(int* a, int * b)
{
    *a += *b;
    return *a;
}/*@
    
    */
    
void goo10() {
    int a = 10;
    int b = 20;
    incr_a_by_b(&a, &b);
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
}