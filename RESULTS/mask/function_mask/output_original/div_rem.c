

/*@
 requires \valid(q) && \valid(r) ;
 requires \separated(q,r) ;

ensures *q == x / y&&*r == x % y;

*/

void div_rem(unsigned x, unsigned y, unsigned* q, unsigned* r) 
{
    *q = x / y;
    *r = x % y;
}