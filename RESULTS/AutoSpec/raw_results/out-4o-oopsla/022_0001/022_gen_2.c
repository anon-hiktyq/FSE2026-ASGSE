int unknown();

void foo022() {
  int x = 0;
  int y = 0;
  int z = 0;
  int k = 0;

  /*@
  loop invariant x <= y;
  loop invariant y <= z;
  loop invariant 3 * x >= z;
  loop invariant k == x + y + z;
  loop assigns x;
  loop assigns y;
  loop assigns z;
  loop assigns k;
  */
  while(unknown())
  {
     if(k%3 == 0){
        x++;
     }
      
     y++;
     z++;
     k = x+y+z;
  }

  // @ assert x == y && y == z ;
 
}
