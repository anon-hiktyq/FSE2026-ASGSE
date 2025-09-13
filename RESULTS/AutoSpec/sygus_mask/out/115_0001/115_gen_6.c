int main() {
  int sn = 0;
  int x = 0;
  
  /*@
  loop invariant sn == x;
  loop invariant sn >= 0;
  loop invariant x >= 0;
  loop assigns sn;
  loop assigns x;
  */
  while (unknown()) {
    x  = x + 1;
    sn  = sn + 1;
  }

}
