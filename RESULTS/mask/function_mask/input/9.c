void order_3(int *a, int *b, int *c) {
    if (*a > *b) {
        int temp = *a;
        *a = *b;
        *b = temp;
    }
    if (*a > *c) {    
        int temp = *a;
        *a = *c;
        *c = temp;
    }
    if (*b > *c) {
        int temp = *b;
        *b = *c;
        *c = temp;
    }
}

void goo9(){
    
    int a1 = 5, b1 = 3, c1 = 4 ;
    order_3(&a1, &b1, &c1) ;
/* MASK_ACSL_ASSERT_LINE */
    
    int a2 = 2, b2 = 2, c2 = 2 ;
    order_3(&a2, &b2, &c2) ;
/* MASK_ACSL_ASSERT_LINE */

    int a3 = 4, b3 = 3, c3 = 4 ;
    order_3(&a3, &b3, &c3) ;
/* MASK_ACSL_ASSERT_LINE */

    int a4 = 4, b4 = 5, c4 = 4 ;
    order_3(&a4, &b4, &c4) ;
/* MASK_ACSL_ASSERT_LINE */
}