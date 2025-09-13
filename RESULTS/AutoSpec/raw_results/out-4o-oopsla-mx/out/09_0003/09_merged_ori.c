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
  loop invariant true;
  loop invariant k == n - j;
  loop invariant k == i;
  loop invariant k == i - t;
  loop invariant k == i - t + 1;
  loop invariant k + j == n;
  loop invariant k + i == n;
  loop invariant j >= 0 && j <= n;
  loop invariant j <= n;
  loop invariant j + i == n;
  loop invariant i == n - j;
  loop invariant i + j == n;
  loop invariant 0 <= n;
  loop invariant 0 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant -j <= k;
  loop invariant -1 <= k;
  loop assigns t;
  loop assigns k;
  loop assigns j;
  loop assigns i;
  loop assigns \nothing;
  ```c;
  ```;
  For the second `while` loop:;
  For the first `while` loop:;
  For the final `while` loop:;
  /* Loop invariant for the third while loop */;
  /* Loop invariant for the second while loop */;
  /* Loop invariant for the fourth while loop */;
  /* Loop invariant for the first while loop */;
  /* Loop invariant for the final while loop */;
  /* Invariant for the third loop */;
  /* Invariant for the third loop (final loop) */;
  /* Invariant for the second while loop */;
  /* Invariant for the second loop */;
  /* Invariant for the fourth loop */;
  /* Invariant for the first while loop */;
  /* Invariant for the first loop */;
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
