



/*@
 requires \valid(a) && \valid(b) ;

ensures *a == \old(*a) + \old(*b)&&*b == \old(*b);
ensures \result == \old(*a) + \old(*b);

*/

int incr_a_by_b(int* a, int * b)
{
    *a += *b;
    return *a;
}
void moo16() 
{
    int a = 10;
    int b = 20;
    incr_a_by_b(&a, &b);
    //@ assert a == 30;
    //@ assert b == 20;
}