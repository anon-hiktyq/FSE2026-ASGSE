/*@
requires \valid(b);
requires \valid(a);
requires \valid(a) && \valid_read(b);
requires \valid(a) && \valid(b);
requires \separated(a, b);
ensures \result == *a;
ensures *b == \old(*b);
ensures *a == \old(*a) + *b;
assigns *a;
*/
int incr_a_by_b(int* a, int const* b){
    *a += *b;
    return *a;
}

// write a test
void main() {
    int a = 10;
    int b = 20;
    incr_a_by_b(&a, &b);
    //@ assert a == 30;
    //@ assert b == 20;
}