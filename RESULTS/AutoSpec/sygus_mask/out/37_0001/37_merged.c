int unknown();

int main() {
  int c = 0;

  /*@
  loop invariant c == 40 ==> \exists integer k; k == 1;
  loop invariant c <= 40;
  loop invariant c != 40 ==> \forall integer k; c < 40;
  loop invariant \forall integer k; c == 40 ==> \exists integer m; m < k;
  loop invariant \forall integer k; c == 40 ==> (\exists integer m; m > 0 && m < 40 ==> c == m);
  loop invariant \forall int k; k >= 0 ==> (c == 40 ==> \exists int m; m < k && c == 1);
  loop invariant \forall int k; k < c ==> k != 40;
  loop invariant 0 <= c;
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
