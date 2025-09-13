int unknown();

int main() {
  int c = 0;

  /*@
  loop invariant c >= 0;
  loop invariant c <= 40;
  loop invariant \forall integer k; c == 40 ==> (\exists integer m; m > 0 && m < 40 ==> c == m);
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
