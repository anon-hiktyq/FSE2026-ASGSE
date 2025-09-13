
/*@
  requires \valid(a) && \valid(b);
  requires \separated(a, b);

  ensures \old(*a) < \old(*b) ==> *a == \old(*a) && *b == \old(*b);
  ensures \old(*a) < \old(*b) ==> \result == \old(*b);

  ensures \old(*a) >= \old(*b) ==> *a == \old(*a) && *b == \old(*b);
  ensures \old(*a) >= \old(*b) ==> \result == \old(*a);
*/
int max_ptr(int *a, int *b)
{
    return (*a < *b) ? *b : *a;
}

/*@ 
  ensures \result == 0;
*/
int goo15() {
    h = 42;
    int a = 24;
    int b = 42;

    int x = max_ptr(&a, &b);

/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
    return 0;
}
