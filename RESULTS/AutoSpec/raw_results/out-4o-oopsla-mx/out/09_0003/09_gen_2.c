#include <assert.h>

int unknown1();
int unknown2();
int unknown3();

/*
 * "fragtest_simple" from InvGen benchmark suite
 */

int main(){
  int i, pvlen;
  int t;
  int k = 0;
  int n;
  i = 0;

  //  pkt = pktq->tqh_first;
  /*@
  ```c
  /* Invariant for the first loop */
  loop invariant i >= 0;
  loop assigns i;
  
  /* Invariant for the second loop */
  loop invariant i >= 0;
  loop invariant k >= 0;
  loop assigns i, k, t;
  
  /* Invariant for the third loop */
  loop assigns \nothing;
  
  /* Invariant for the fourth loop */
  loop invariant k >= 0;
  loop invariant i >= 0;
  loop invariant j >= 0;
  loop invariant j <= n;
  loop invariant k + i == n;
  loop assigns k, i, j;
  ```
  */
  while (unknown1())
    i = i + 1;
  
  if (i > pvlen) {
    pvlen = i;
  } else {

  }
  i = 0;

  while (unknown2()) {
    t = i;
    i = i + 1;
    k = k + 1;
  }
  while (unknown3());

  int j = 0;
  n = i;
  while (1) {
    // @ assert k >= 0;
    k = k - 1;
    i = i - 1;
    j = j + 1;
    if (j < n) {
    } else {
      break;
    }
  }
  return 0;
}
