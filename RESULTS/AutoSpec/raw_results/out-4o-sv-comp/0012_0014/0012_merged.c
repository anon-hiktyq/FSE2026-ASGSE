
#include <limits.h>

int unknown1();

/*@
requires l > 0;
requires l < INT_MAX;
requires n < INT_MAX;
*/
void foo0012(int n, int l) {
  int k = 1;

  
  /*@
  loop invariant l > 0 && l < INT_MAX;
  loop invariant l <= INT_MAX;
  loop invariant l < INT_MAX;
  loop invariant k > 0 && k < INT_MAX;
  loop invariant k <= n;
  loop invariant k <= INT_MAX;
  loop invariant \forall integer m; l <= m <= n ==> m < INT_MAX;
  loop invariant \forall integer m; l <= m < n ==> 1 <= m;
  loop invariant \forall integer m; l <= m < k ==> n < INT_MAX;
  loop invariant \forall integer m; l <= m < k ==> m >= l;
  loop invariant \forall integer m; l <= m < k ==> m > 0;
  loop invariant \forall integer m; 1 <= m < k ==> n < INT_MAX;
  loop invariant \forall integer m; 1 <= m < k ==> m < n;
  loop invariant \forall integer j; 1 <= j < k ==> n < INT_MAX;
  loop invariant \forall integer j; 1 <= j < k ==> l + j <= n || l + j >= n;
  loop invariant \forall integer j; 1 <= j < k ==> j >= 1;
  loop invariant \forall integer j; 1 <= j < k ==> j < n;
  loop invariant \forall integer j; 1 <= j < k ==> 1 <= j;
  loop invariant \forall integer j; 1 <= j < k ==> 0 < l <= n;
  loop invariant 1 <= l;
  loop invariant 0 <= k;
  loop invariant 0 < l && k >= 1;
  loop invariant n < INT_MAX;
  loop invariant k < INT_MAX;
  loop invariant \forall integer m; l <= m <= n ==> 1 <= m;
  loop invariant \forall integer m; 1 <= m <= n ==> n < INT_MAX;
  loop invariant \forall integer m; 1 <= m < l ==> m > 0;
  loop invariant \forall integer m; 1 <= m < k ==> n <= INT_MAX;
  loop invariant \forall integer m; 1 <= m < k ==> m >= 1;
  loop invariant \forall integer m; 1 <= m < k ==> l <= INT_MAX;
  loop invariant 1 <= k;
  loop invariant 0 < l;
  loop assigns l;
  loop assigns k;
  */
  for (; k < n; k++){

    int i= l;
    
    /*@
    loop invariant n < INT_MAX;
    loop invariant n < INT_MAX && k < INT_MAX;
    loop invariant l <= i;
    loop invariant l <= INT_MAX;
    loop invariant l < INT_MAX;
    loop invariant k < n;
    loop invariant i <= n;
    loop invariant i <= INT_MAX;
    loop invariant i < INT_MAX;
    loop invariant \forall integer m; l <= m <= i ==> 1 <= m;
    loop invariant \forall integer m; l <= m < i ==> m >= l;
    loop invariant \forall integer m; l <= m < i ==> m < n;
    loop invariant \forall integer m; l <= m < i ==> 1 <= m;
    loop invariant \forall integer m; l <= m < i ==> 0 <= m;
    loop invariant 1 <= i;
    loop invariant 0 < l;
    loop invariant 0 < l && l < INT_MAX;
    loop assigns i;
    */
    for (; i < n; i++){
      // @ assert 1 <= i;*/
    }
    if(unknown1()) {
      l = l + 1;
    }
  }
}
