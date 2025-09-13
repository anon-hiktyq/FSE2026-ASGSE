
void foo010() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  /*@
    loop invariant z <= 1;
    loop invariant w == 1 || w == 0;
    loop invariant 0 <= x;
    loop invariant 0 <= y;
    loop assigns x;
    loop assigns y;
    loop assigns z;
    loop assigns w;
  */
  while(unknown()){
    if(w) {
      x++;
      w = !w;
    }

    if(!z) {
      y++; 
      z=!z;
    }
  }

  /*@ assert x == y; */
  
}
