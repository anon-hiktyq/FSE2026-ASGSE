
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
  loop invariant k < INT_MAX;
  loop invariant 1 <= k;
  loop invariant 0 < l;
  loop assigns l;
  loop assigns k;
  */
  for (; k < n; k++){

    int i= l;
    
    /*@
    loop invariant i <= n;
    loop invariant l <= i;
    loop invariant 1 <= i;
    loop invariant k <= n;
    loop invariant k < n;
    loop invariant 0 <= i;
    loop invariant 0 < l;
    loop invariant \forall integer j; l <= j < i ==> j < n;
    loop invariant l <= i;
    loop invariant k <= n;
    loop invariant k < n;
    loop invariant 1 <= k;
    loop invariant 1 <= i;
    loop invariant 0 <= k;
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
