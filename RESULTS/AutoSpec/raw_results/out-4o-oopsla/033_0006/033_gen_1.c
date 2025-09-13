int unknown1();
int unknown2();
int unknown3();

void foo033(int k) {
  int z = k;
  int x = 0;
  int y = 0;

 
  /*@
  loop invariant z == k + y;
  loop invariant x == z - k;
  loop invariant x == y;
  loop invariant x == y + (k - z);
  loop invariant x >= 0;
  loop invariant y >= 0;
  loop invariant z >= k;
  loop assigns z, x, y;
  */
  while(unknown1())
  {
    int c = 0;
    /*@
    loop invariant z == k + y;
    loop invariant z - k <= y + c;
    loop invariant y - c <= z - k;
    loop invariant x == z - k;
    loop invariant x == y;
    loop invariant x == y + (k - z);
    loop invariant \forall integer n; 0 <= n <= c ==> (z == k + y - n || z == k + y + n);
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant 0 <= c;
    loop invariant -k <= y;
    loop assigns z;
    loop assigns y;
    loop assigns x;
    loop assigns c;
    */
    while(unknown2())
    {
      if(z==k+y-c)
      {
        x++;
        y++;
        c++;
      }else
      {
        x++;
        y--;
        c++;
      }
    }

    /*@
    loop invariant z == k + y;
    loop invariant x == z - k;
    loop invariant x == y;
    loop invariant x == y + (k - z);
    loop invariant x + y == c;
    loop invariant x + y == 2 * z - 2 * k;
    loop invariant k <= z;
    loop invariant \forall integer n; 0 <= n <= c ==> (x == y - n || x == y + n);
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop assigns z;
    loop assigns y;
    loop assigns x;
    */
    while(unknown3())
    {
      x--;
      y--;
    }
    z=k+y;
  }

  // @ assert x==y;
}
