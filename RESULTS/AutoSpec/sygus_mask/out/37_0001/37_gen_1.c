int unknown();

int main() {
  int c = 0;

  /*@
  loop invariant c >= 0;
  loop invariant c <= 40;
  loop invariant c == 40 ==> \exists integer k; k >= 1; c == k;
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
