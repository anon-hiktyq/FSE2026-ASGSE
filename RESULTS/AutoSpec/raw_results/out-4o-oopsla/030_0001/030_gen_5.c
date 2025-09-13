
void foo030() {

  int i, c;
  i = 0;
  c = 0;
 
  /*@
  loop invariant 0 <= i <= 1000;
  loop invariant c == i * (i - 1) / 2;
  loop invariant c >= 0;
  loop assigns i, c;
  */
  while (i < 1000) {
    c = c + i;
    i = i + 1;
  }

  // @ assert c >= 0;
}

