
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
  loop invariant 1 <= k <= n;
  loop invariant l > 0;
  loop invariant l < INT_MAX;
  loop invariant n < INT_MAX;
  loop invariant k < n;
  loop assigns k;
  loop assigns l;
  */
  for (; k < n; k++){

    int i= l;
    
    /*@
    loop invariant l <= i;
    loop invariant k < n;
    loop invariant i <= n;
    loop invariant i < INT_MAX;
    loop invariant 1 <= i;
    loop invariant 0 <= k;
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
