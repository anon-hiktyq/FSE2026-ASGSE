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
    loop invariant x == y + (k - z);
    loop invariant z == k + y;
    loop invariant 0 <= c;
    loop assigns x, y, z, c;
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

    while(unknown3())
    {
      x--;
      y--;
    }
    z=k+y;
  }

  // @ assert x==y;
}
