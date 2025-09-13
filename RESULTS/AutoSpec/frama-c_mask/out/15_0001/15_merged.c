
/*@
requires y != 0;
requires \valid(r);
requires \valid(q);
requires \separated(q, r);
ensures x == *q * y + *r;
ensures *r == x % y;
ensures *r < y;
ensures *q == x / y;
assigns *q, *r;
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