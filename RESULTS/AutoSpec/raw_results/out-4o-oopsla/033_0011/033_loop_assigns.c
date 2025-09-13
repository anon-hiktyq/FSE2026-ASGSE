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
    loop invariant x == y;
    loop invariant x == y + c;
    loop invariant \forall integer i; 0 <= i <= c ==> z == k + y - i;
    loop invariant \forall integer i; 0 <= i <= c ==> z == k + y - i || z == k + y + i;
    loop invariant \forall integer i; 0 <= i <= c ==> (z == k + y - i) || (z == k + y + i);
    loop invariant \forall integer i; 0 <= i <= c ==> (z == k + y - i || z == k + y);
    loop invariant \forall integer d; c >= d ==> z == k + y - d;
    loop invariant \exists integer d; d >= 0 && d == c;
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
    loop assigns z;
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
