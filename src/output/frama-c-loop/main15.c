


/*@
  requires \valid(arr + (0 .. n-1)); 
  ensures \forall int j; 0 <= j < n ==> arr[j] == \old(arr[j]) + c;
*/

void increment_array_by(int* arr, int n, int c) {
    /*@
      loop invariant (\forall int j; 0 <= j < i ==> arr[j] == \at(arr[j],Pre) + c);
      loop invariant (\forall int k; i <= k < n ==> arr[k] == \at(arr[k],Pre));
      loop invariant c == \at(c,Pre);
      loop invariant n == \at(n,Pre);
      loop invariant arr == \at(arr,Pre);
      loop variant n-i;
    */
    for (int i = 0; i < n; i++) {
        arr[i] = arr[i] + c;
    }
}

void main15() {
    int arr[5] = {1, 2, 3, 4, 5};
    increment_array_by(arr, 5, 2);
    //@ assert arr[0] == 3;
    //@ assert arr[1] == 4;
    //@ assert arr[2] == 5;
    //@ assert arr[3] == 6;
    //@ assert arr[4] == 7;
}