int unknown();

int main() {
  int c = 0;

  /*@
  loop invariant c >= 0;
  loop invariant c <= 40;
  loop invariant \forall integer k; 0 <= k < c ==> c != 40;
  loop invariant (c == 40) ==> \exists integer k; c == 1;
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
