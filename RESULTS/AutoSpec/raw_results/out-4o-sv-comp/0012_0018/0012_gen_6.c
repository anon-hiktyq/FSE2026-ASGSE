
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
  loop invariant k <= n;
  loop invariant l <= i;
  loop invariant l <= INT_MAX;
  loop invariant k <= INT_MAX;
  loop invariant 1 <= k;
  loop invariant 1 <= l;
  loop invariant n < INT_MAX;
  loop invariant \forall integer j; 1 <= j < k ==> 0 < l;
  loop invariant \forall integer m; k <= m < l ==> 1 <= m;
  loop invariant n < INT_MAX;
  loop invariant l <= INT_MAX;
  loop invariant 1 <= l;
  loop invariant 1 <= k;
  loop invariant 0 < l;
  loop assigns l;
  loop assigns k;
  */
  for (; k < n; k++){

    int i= l;
    
    /*@
    loop invariant l <= i;
    loop invariant l <= INT_MAX;
    loop invariant k <= n;
    loop invariant k <= i;
    loop invariant k <= INT_MAX;
    loop invariant k < n;
    loop invariant i <= n;
    loop invariant i <= INT_MAX;
    loop invariant i < INT_MAX;
    loop invariant \forall integer m; k <= m < i ==> 1 <= m;
    loop invariant \forall integer j; k <= j < n ==> 1 <= i;
    loop invariant 1 <= l;
    loop invariant 1 <= k;
    loop invariant 1 <= i;
    loop invariant 0 < l;
    loop invariant 0 < i;
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
