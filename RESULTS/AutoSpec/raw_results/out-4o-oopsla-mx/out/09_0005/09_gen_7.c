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
  For the first loop:
  ```c
  loop invariant i >= 0;
  loop assigns i;
  ```
  
  For the second loop:
  ```c
  loop invariant i >= 0;
  loop invariant k >= 0;
  loop invariant i == t + k;
  loop assigns i, t, k;
  ```
  
  For the final loop:
  ```c
  loop invariant k >= -1;
  loop invariant j >= 0;
  loop invariant j <= n;
  loop invariant i >= 0;
  loop invariant j + i == n;
  loop assigns i, j, k;
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
