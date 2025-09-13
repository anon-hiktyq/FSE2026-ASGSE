/*@
requires \valid(a) && \valid(b);
ensures \result >= *a && \result >= *b;
ensures \result == *b ==> *b >= *a;
ensures \result == *a || \result == *b;
ensures \result == *a ==> *a >= *b;
ensures *a > *b ==> \result == *a;
ensures *a <= *b ==> \result == *b;
ensures (*b > *a) ==> (\result == *b);
ensures (*a >= *b) ==> (\result == *a);
ensures (*a < *b) ==> (\result == *b);
assigns \nothing;
*/
int max_ptr(int *a, int *b){
    return (*a < *b) ? *b : *a ;
}

extern int h;

int moo17() {
    h = 42;
    int a = 24;
    int b = 42;

    int x = max_ptr(&a, &b);

    //@ assert x == 42;
    //@ assert h == 42;
    return 0;
}