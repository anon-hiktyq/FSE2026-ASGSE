
/*@ axiomatic Max_array {
      logic integer max(int* array, integer begin, integer end) reads array[begin .. (end-1)];
      axiom empty:
        \forall int* a, integer b, e; b >= e ==> max(a,b,e) == a[b];
      axiom range:
        \forall int* a, integer b, e; b < e ==> max(a,b,e) == (max(a,b,e-1) < a[e-1] ? a[e-1] : max(a,b,e-1));
    }
*/

/*@
requires \valid(a + (0 .. n-1));
requires n > 0 && n < 100;
*/
int arraymax(int* a, int n) {
  int i = 1;
  int max = a[0];

  /* >>> LOOP INVARIANT TO FILL <<< */
  
  /*@
    loop invariant (1 < \at(n,Pre)) ==> (1 <= i <= n);
    loop invariant (1 < \at(n,Pre)) ==> (((max == a[0])&&(i == 1)&&(n == \at(n,Pre))&&(a == \at(a,Pre))) || (max == max(a, 0, i)));
    loop invariant (!(1 < \at(n,Pre))) ==> ((max == a[0])&&(i == 1)&&(n == \at(n,Pre))&&(a == \at(a,Pre)));
    loop invariant n == \at(n,Pre);
    loop invariant a == \at(a,Pre);
    loop invariant \forall integer j; 0 <= j < n ==> a[j] == \at(a[j], Pre);
  */
  while (i < n) {
    if (max < a[i])
      max = a[i];
    i = i + 1;
  }
  
  return max;
}
