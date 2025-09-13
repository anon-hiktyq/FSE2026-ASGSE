// Program to find index of an element in an array
// Behaviors not used in this program

int array_find(int* arr, int n, int x) {
    int i = 0;

    /*@
    loop invariant i == n ==> \forall integer k; 0 <= k < n ==> arr[k] != x;
    loop invariant i == n ==> (\forall integer k; 0 <= k < n ==> arr[k] != x).;
    loop invariant i <= n;
    loop invariant \result == -1 ==> \forall integer k; 0 <= k < n ==> arr[k] != x;
    loop invariant \forall integer k; i <= k < n ==> arr[k] != x ==> index == -1;
    loop invariant \forall integer k; i <= k < n ==> arr[k] != x ==> (x < n);
    loop invariant \exists integer k; i <= k < n ==> arr[k] == x || i == n;
    loop invariant \exists integer k; 0 <= k < n ==> (arr[k] == x || \forall integer j; 0 <= j < i ==> arr[j] != x);
    loop invariant \exists integer k; 0 <= k < i ==> (arr[k] == x) || i == n;;
    loop invariant \exists integer k; 0 <= k < i ==> (arr[k] == x || arr[k] != x);
    loop invariant \exists integer k; 0 <= k < i ==> (arr[k] == x || \forall integer j; 0 <= j < i ==> arr[j] != x);
    loop invariant \exists integer k; 0 <= k < i <==> arr[k] == x ==> (\forall integer j; 0 <= j < k ==> arr[j] != x);
    loop invariant \exists integer k; 0 <= k < i && arr[k] == x ==> \result == k;
    loop invariant \exists integer j; 0 <= j < n ==> (arr[j] == x || \forall integer k; 0 <= k < i ==> arr[k] != x);
    loop invariant (i == n) ==> \forall integer k; 0 <= k < n ==> arr[k] != x;;
    loop invariant (i == n) ==> (\forall integer j; 0 <= j < n ==> arr[j] != x);
    loop invariant \forall integer k; 0 <= k < i ==> arr[k] != x;
    loop invariant 0 <= i;
    loop assigns i;
    */
    for (i = 0; i < n; i++) {
        if (arr[i] == x) {
            return i;
        }
    }
    return -1;
}

// write a test
void main() {
    int arr[5] = {1, 2, 3, 4, 5};
    int index = array_find(arr, 5, 3);
    // @ assert index == 2;
}