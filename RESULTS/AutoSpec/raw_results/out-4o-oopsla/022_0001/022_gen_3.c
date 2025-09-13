int unknown();

void foo022() {
  int x = 0;
  int y = 0;
  int z = 0;
  int k = 0;

  /*@
  loop invariant x <= y && y <= z;
  loop invariant x <= z;
  loop invariant k == x + y + z;
  loop invariant k % 3 == (x % 3 + y % 3 + z % 3) % 3;
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
