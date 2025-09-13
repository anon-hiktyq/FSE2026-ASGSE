


/*@
 requires \valid(a) && \valid(b) ;

ensures \old(*b) != 0 ==> *a == 0&&*b == \old(*b);

ensures \old(*b) == 0 ==> *a == \old(*a)&&*b == \old(*b);

*/

void reset_1st_if_2nd_is_true(int* a, int const* b)
{
    if(*b) *a = 0 ;
}