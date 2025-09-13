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
/*@ requires \valid(arr+(0..4));*/
int subArray(int arr[5]) 
{
    int sum = 0;  
    int i =0; 
    

            
            /*@
          loop invariant \valid(arr+(0..4)) ;
          loop invariant  sum == -sum(arr, 0, i) ;
          loop invariant  0 <= i <= 5 ;
          loop invariant arr == \at(arr,Pre);
            */
            for (; i < 5; i++) {
    sum -= arr[i];
}
            
        
return sum;
}