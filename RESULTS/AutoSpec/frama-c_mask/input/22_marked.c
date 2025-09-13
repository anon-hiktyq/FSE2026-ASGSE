
/* 2. FUNC CONTRACT */
void func(int *a, int n) {
   
    /* 1. LOOP INVARIANT */
    for (int i = 0; i < n; i++) {
        if (i%2==0) 
            a[i] = 0;
    }
}

// write a test
/* 3. FUNC CONTRACT */
void main() {
    int arr[5] = {1, 2, 3, 4, 5};
 
}