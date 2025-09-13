int unknown1();
int unknown2();
int unknown3();

void foo033(int k) {
  int z = k;
  int x = 0;
  int y = 0;

 
  while(unknown1())
  {
    int c = 0;
    /*@
    loop invariant z == k + y;
    loop invariant z == k + y - c;
    loop invariant y == z - k;
    loop invariant x == z - k;
    loop invariant x == y;
    loop invariant k <= z;
    loop invariant c <= y;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant 0 <= c;
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
    loop invariant x == y;
    loop invariant z == k + y;
    loop invariant y >= 0;
    loop invariant x >= 0;
    loop assigns x;
    loop assigns y;
    loop assigns z;
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
