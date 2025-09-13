
/*@ axiomatic Sum_array {
    logic integer sum(int* array, integer begin, integer end)
        reads array[begin .. (end-1)];
    
    axiom empty:
        \forall int* a, integer b, e;
        b >= e ==> sum(a,b,e) == 0;
    
    axiom range:
        \forall int* a, integer b, e;
        b < e ==> sum(a,b,e) == sum(a,b,e-1) + a[e-1];
}*/
int sumArray(int arr[5]) {
    int sum = 0;
    
        
        /*@
      loop invariant 0 <= i <= 5 ;
      loop invariant (i < 5) ==> (sum == sum(arr, 0, i)) ;
      loop invariant (!(i < 5)) ==> (sum == sum(arr, 0, i)) ;
      loop invariant arr == \at(arr,Pre);
        */
        for (int i = 0; i < 5; i++) {
    sum += arr[i];
}
        
return sum;
}
