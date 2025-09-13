
#include <limits.h>

int unknown1();

/*@
requires l > 0;
requires l < INT_MAX;
requires n < INT_MAX;
*/
void foo0012(int n, int l) {
  int k = 1;

  
  for (; k < n; k++){

    int i= l;
    
    /*@
    loop invariant 1 <= k <= n;
    loop assigns k, l;
    loop invariant l > 0;
    loop assigns i;
    loop invariant l <= i <= n;
    loop invariant i >= l;
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
