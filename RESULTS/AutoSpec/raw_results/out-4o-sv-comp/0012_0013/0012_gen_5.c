
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
    loop invariant l <= i <= n;
    loop invariant k < n;
    loop invariant \forall integer m; l <= m < i ==> 1 <= m;
    loop invariant 1 <= i <= n;
    loop invariant 0 < l;
    loop invariant i <= n;
    loop assigns i;
    loop invariant l <= i;
    loop invariant k < n;
    loop invariant \forall integer m; l <= m < i ==> 1 <= m;
    loop invariant 1 <= i;
    loop invariant 0 < l;
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
