
void foo65() {
  int a = 1;
  int b = 1;
  int c = 2;
  int d = 2;
  int x = 3;
  int y = 3;
 
  /*@
    loop invariant (x + y) % 2 == 0 || (x + y) % 2 == 1;
  */
  while (unknown1()) {
    x = a + c;
    y = b + d;

    if ((x + y) % 2 == 0) {
      a++;
      d++;
    } else {
      a--;
    }

    
    while (unknown2()) {
      c--;
      b--;
    }
  }
  /*@assert a + c == b + d ;*/
}
