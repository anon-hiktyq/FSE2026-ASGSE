int unknown();

void foo022() {
  int x = 0;
  int y = 0;
  int z = 0;
  int k = 0;

  /*@
  loop invariant z == y;
  loop invariant z <= x + 1;
  loop invariant z <= 3 * x;
  loop invariant z - y == y - x;
  loop invariant y == z;
  loop invariant y <= z;
  loop invariant x <= z;
  loop invariant x <= y;
  loop invariant x <= y && y <= z;
  loop invariant x + y + z == k;
  loop invariant k == x + y + z;
  loop invariant k % 3 == 0 ==> x == y == z;
  loop invariant k % 3 == (x % 3 + y % 3 + z % 3) % 3;
  loop invariant \exists integer n; n >= 0 && k == 3 * n + (x + y + z);
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= k;
  loop assigns z;
  loop assigns y;
  loop assigns x;
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

  //@ assert x == y && y == z ;
 
}
