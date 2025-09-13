int unknown();

int main() {
  int c = 0;
  
  /*@
  loop invariant c <= 40;
  loop invariant \exists integer k; k <= 40 ==> (c == 40 ==> c == 1) || (c != 40 ==> c == k + 1);
  loop invariant 0 <= c;
  loop invariant (c != 40) ==> ( \forall integer k; c < 40);
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
