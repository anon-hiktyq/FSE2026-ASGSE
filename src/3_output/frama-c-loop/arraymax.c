
int arraymax(int* a, int n) {
  int i = 1;
  int max = a[0];

  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant \forall integer j; 0 <= j < i ==> a[j] <= max; // All processed elements are less than or equal to max
              loop variant n - i; // Ensure the loop will terminate
            */
            while (i < n) {
    if (max < a[i])
    max = a[i];
    i = i + 1;
  }
            
  return max;
}
