int unknown1();
int unknown2();
int unknown3();

void foo033(int k) {
  int z = k;
  int x = 0;
  int y = 0;

 
  /*@
  loop invariant z == k + y;
  loop invariant x == y;
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
    loop invariant x == y;
    loop invariant x == y + c;
    loop invariant \forall integer m; 0 <= m <= c ==> z == k + y - m;
    loop invariant \forall integer m; 0 <= m <= c ==> (z == k + y - m || z == k + y + m);
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
    loop invariant z == k + y;
    loop invariant y <= x;
    loop invariant x == y;
    loop invariant x == y + c;
    loop invariant x <= y + c;
    loop invariant x - y == \at(x - y, LoopEntry);
    loop invariant x - y == 0;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant 0 <= c;
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
