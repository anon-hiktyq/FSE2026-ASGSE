
/*@
  requires n >= 0;                     // Input constraint: n must be non-negative
  requires n <= CHAR_MAX;             // Input constraint: n must not exceed the maximum value of a char
  ensures \result == \sum_{i=0}^{n} i; // Postcondition: the result is the sum of integers from 0 to n
*/
int sum(char n) {
    int s = 0;
    char k = 0;

    /*@
      loop invariant 0 <= k;                        // k is non-negative
      loop invariant k <= n + 1;                    // k does not exceed n + 1
      loop invariant s == \sum_{i=0}^{k-1} i;       // s holds the sum of integers from 0 to k-1
      loop variant n - k;                           // The loop progresses as k approaches n
    */
    while(k <= n) {    
        s = s + (int)k;
        k = k + 1;
    }
            
    return (int)s;
}
