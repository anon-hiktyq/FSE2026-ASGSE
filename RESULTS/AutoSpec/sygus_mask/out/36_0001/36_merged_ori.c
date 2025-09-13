int unknown();

int main() {
  int c = 0;

  /*@
  loop invariant c >= 0 && c <= 40;
  loop invariant c <= 40;
  loop invariant c != 40 ==> \forall integer k; c < k <= 40 ==> c < k;
  loop invariant \forall integer k; 0 <= k < c ==> k != 40;
  loop invariant \exists integer k; c == k ==> k <= 40;
  loop invariant 0 <= c;
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c != 40) {
        c  = c + 1;
      }
    } else {
      if (c == 40) {
        c  = 1;
      }
    }
  }

}
