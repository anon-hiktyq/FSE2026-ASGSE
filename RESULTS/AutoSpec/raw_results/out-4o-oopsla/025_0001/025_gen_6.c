
int unknown1();
int unknown2();


void foo025() {
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

 
  while(unknown1())
  {
    
    /*@
    loop invariant 0 <= i;
    loop invariant 0 <= j;
    loop invariant 0 <= x && 0 <= y;
    loop invariant i >= j;
    loop invariant x == y || x == y + 1;
    loop assigns i, j;
    loop assigns x, y;
    */
    while(unknown2())
    {
       if(x == y){
          i++;
       }else{
          j++;
       }
    }

    if(i >= j)
    {
       x++;
       y++;
    }
    else{
       y++;
    }
  }

  // @ assert i >= j;
}
