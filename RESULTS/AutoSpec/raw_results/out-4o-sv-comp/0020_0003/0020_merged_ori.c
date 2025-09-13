
/*@
requires 0 <= n && n < 2;
requires 0 <= v;
*/
void foo0020(int n, int v) {
  int c1 = 4000;
  int c2 = 2000;
  int c3 = 10000;
  
  int i, k, j;

  k = 0;
  i = 0;

  /*@
  loop invariant n - j <= k;
  loop invariant k == (n-j) * (v == 0 ? c1 : (v == 1 ? c2 : c3));
  loop invariant k % ((v == 0) ? c1 : ((v == 1) ? c2 : c3)) == 0;
  loop invariant j <= n;
  loop invariant j <= k;
  loop invariant i * ((v == 0) ? c1 : (v == 1) ? c2 : c3) >= 0;
  loop invariant i * ((v == 0 ? c1 : (v == 1 ? c2 : c3))) >= 0;
  loop invariant \forall integer j; 0 <= j < i ==> k > j * (v == 0 ? c1 : v == 1 ? c2 : c3);
  loop invariant 0 <= n - j;
  loop invariant 0 <= k;
  loop invariant 0 <= j;
  loop invariant -1 < k;
  loop invariant (v >= 2) ==> k == i * c3;
  loop invariant (v == 1) ==> k == i * c2;
  loop invariant (v == 0) ==> k == i * c1;
  loop invariant (v == 0 && k == i * 4000) || (v == 1 && k == i * 2000) || (v >= 2 && k == i * 10000);
  loop invariant (v == 0 && k == (n-j) * c1) || (v == 1 && k == (n-j) * c2) || (v >= 2 && k == (n-j) * c3);
  loop invariant (n - j) < k;
  loop invariant k == i * (v == 0 ? c1 : v == 1 ? c2 : c3);
  loop invariant k == i * (v == 0 ? c1 : (v == 1 ? c2 : c3));
  loop invariant k == i * ((v == 0) ? c1 : ((v == 1) ? c2 : c3));
  loop invariant i <= n;
  loop invariant i * ((v == 0) ? c1 : ((v == 1) ? c2 : c3)) >= 0;
  loop invariant 0 <= i;
  loop invariant (v == 0 && k == i * c1) || (v == 1 && k == i * c2) || (v >= 2 && k == i * c3);
  loop assigns k;
  loop assigns i;
  */
  while (i < n) {
    i++;
    if (v == 0)
      k += c1;
    else if (v == 1)
      k += c2;
    else
      k += c3;
  }

  j = 0;

  /*@
  loop invariant j <= n;
  loop invariant 0 <= n - j;
  loop invariant 0 <= j;
  loop assigns k;
  loop assigns j;
  */
  while (j < n) {
    // @ assert k > 0;
    j++;
    k--;
  }

}
