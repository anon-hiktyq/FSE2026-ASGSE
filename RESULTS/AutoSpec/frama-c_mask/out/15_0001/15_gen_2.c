
/*@
requires \valid(q) 
requires \valid(r);
requires \separated(q, r);
requires y != 0;
assigns *q, *r;
ensures x == *q * y + *r;
ensures *r < y;

void main() {
    unsigned q, r;
    div_rem(10, 3, &q, &r);
    //@ assert q == 3;
    //@ assert r == 1;

    div_rem(15, 4, &q, &r);
    //@ assert q == 3;
    //@ assert r == 3;

    div_rem(0, 1, &q, &r);
    //@ assert q == 0;
    //@ assert r == 0;

    // Test case to ensure division by zero is not allowed
    // div_rem(10, 0, &q, &r); // This line should not be run, as it would cause undefined behavior
}
*/
void div_rem(unsigned x, unsigned y, unsigned* q, unsigned* r) {
    *q = x / y;
    *r = x % y;
}

// write a test
void main() {
    unsigned q, r;
    div_rem(10, 3, &q, &r);
 
}