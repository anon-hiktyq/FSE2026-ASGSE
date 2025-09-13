
/*@
requires \valid(b);
requires \valid(a);
requires \valid(a) && \valid(b);
ensures \result == *a;
ensures *a == old(*a) + *b;
ensures *a == \old(*a) + *b;
ensures *a == 10 + *b;
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
  
}