int main() {
  int sn = 0;
  int x = 0;
  
  /*@
  loop invariant sn == x;
  loop invariant 0 <= sn;
  loop invariant 0 <= x;
  loop assigns sn, x;
  */
  while (unknown()) {
    x = x + 1;
    sn = sn + 1;
  }
  // post-condition
  if(sn != x) {
    // @ assert sn == -1;
  }
}
