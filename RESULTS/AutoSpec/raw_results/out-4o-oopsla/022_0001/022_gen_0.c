int unknown();

void foo022() {
  int x = 0;
  int y = 0;
  int z = 0;
  int k = 0;

  /*@
  loop invariant x <= y;
  loop invariant x <= z;
  loop invariant y == z;
  loop invariant k == x + y + z;
  loop invariant 0 <= x;
  loop invariant 0 <= y;
  loop invariant 0 <= z;
  loop assigns x, y, z, k;
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
