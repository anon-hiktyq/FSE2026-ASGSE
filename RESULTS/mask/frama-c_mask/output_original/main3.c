



int func3(int *a, int n, int x, int *sum) 
{
    int p = 0;
    int count = 0;
    *sum = 0;

    
            
            /*@
          loop invariant \forall integer i; 0 <= i < \at(n,Pre) ==> a[i] == \at(a[i],Pre) ;
          loop invariant (0 < \at(n,Pre)) ==> (*sum == count * x) ;
          loop invariant (0 < \at(n,Pre)) ==> (0 <= p <= n) ;
          loop invariant (0 < \at(n,Pre)) ==> (0 <= count <= p) ;
          loop invariant x == \at(x,Pre);
          loop invariant n == \at(n,Pre);
          loop invariant a == \at(a,Pre);
          loop invariant count == (\sum integer i; 0 <= i < p && a[i] == x; 1);
          loop invariant *sum == (\sum integer i; 0 <= i < p && a[i] == x; x);
            */
            while (p < n) {
        if (a[p] == x) {
            count = count + 1;
            *sum = *sum + x;
        }
        p = p + 1;
    }
            
    Label_a:
    *sum += 0;
    return count;
}
void main3() 
{
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = 0;
    int count = func3(arr, 5, 3, &sum);
    //@ assert sum == count*3;
}