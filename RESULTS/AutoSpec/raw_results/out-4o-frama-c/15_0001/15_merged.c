/*@
requires y != 0;
requires \valid(r);
requires \valid(q);
requires \valid(q) && \valid(r);
requires \separated(q, r);
ensures x == *q * y + *r;
ensures *r >= 0;
ensures *r < y;
assigns *q, *r;
*/
void div_rem(unsigned x, unsigned y, unsigned* q, unsigned* r) {
    *q = x / y;
    *r = x % y;
}

// write a test
void moo15() {
    unsigned q, r;
    div_rem(10, 3, &q, &r);
    //@ assert q == 3;
    //@ assert r == 1;
   
}