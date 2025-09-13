
/* 2. FUNC CONTRACT */
void arrayDouble(int *a, unsigned int n) {
    int p = 0;


    /* 1. LOOP INVARIANT */
    while (p < n) {
        a[p] = a[p] * 2;
        p = p + 1;
    } 
}

/* 3. FUNC CONTRACT */
int main() {
    int arr[] = {0,1,2,3,4,5};
    arrayDouble(arr, 6);
 
}