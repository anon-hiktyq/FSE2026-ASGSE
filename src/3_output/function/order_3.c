
/*@
    
    */
    
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