int unknown1();
int unknown2();
int unknown3();

void foo033(int k) {
  int z = k;
  int x = 0;
  int y = 0;

 
  /*@
  loop assigns z;
  loop assigns y;
  loop assigns x;
  */
  while(unknown1())
  {
    int c = 0;
    /*@
    loop invariant z == k + y - c;
    loop invariant y == x + c;
    loop invariant y <= x;
    loop invariant y - c <= x;
    loop invariant y - c + 1 == x;
    loop invariant x == y + c;
    loop invariant x + y == z;
    loop invariant k <= z;
    loop invariant k + y == z;
    loop invariant c <= y;
    loop invariant c <= x;
    loop invariant \forall integer m; 0 <= m <= x ==> x - m == y - m;
    loop invariant \forall integer m; 0 <= m <= c ==> z == k + y - m;
    loop invariant \forall integer j; 0 <= j <= c ==> z == k + y - j;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant z == k + y;
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
