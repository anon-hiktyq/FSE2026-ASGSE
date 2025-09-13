int unknown();

void foo022() {
  int x = 0;
  int y = 0;
  int z = 0;
  int k = 0;

  /*@
  loop invariant x <= y;
  loop invariant y <= z;
  loop invariant z <= x + 1;
  loop invariant k == x + y + z;
  loop invariant k % 3 == 0 ==> x == y == z;
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
