
int arraysearch5(int* a, int x, int n) { 

  
            
        /*@ 
          loop invariant (!(p < \at(n,Pre))) ==> ((n == \at(n,Pre))&&(x == \at(x,Pre))&&(a == \at(a,Pre)));
          loop invariant n == \at(n,Pre);
          loop invariant x == \at(x,Pre);
          loop invariant a == \at(a,Pre);
          loop invariant \forall integer i; 0 <= i < p ==> a[i] == \at(a[i], Pre);
          loop assigns p;
        */
            for (int p = 0; p < n; p++) {
    // STart
    if (x == a[p]) 
       return 1;
    // End
  }
            
  return 0;
}
