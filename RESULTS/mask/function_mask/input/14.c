int fun14(int a) {
    int x, y;
    int sum, res;
    if (a == 0){
        x = 0; y = 0;
    }
    else {
        x = 5; y = 5;
    }
    sum = x + y; 
    res = 10/sum; 
    return res;
}

int goo14() {
    int a = fun14(4);
/* MASK_ACSL_ASSERT_LINE */
    return 0;
}