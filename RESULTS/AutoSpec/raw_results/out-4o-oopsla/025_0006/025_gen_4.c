
int unknown1();
int unknown2();


void foo025() {
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

 
  /*@
  loop invariant x <= y;
  loop invariant y <= x + 1;
  loop invariant j <= i;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop assigns x;
  loop assigns y;
  loop assigns j;
  loop assigns i;
  */
  while(unknown1())
  {
    
    /*@
    loop invariant y <= x;
    loop invariant x == y || x == y - 1;
    loop invariant x <= y;
    loop invariant j <= i;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop assigns j;
    loop assigns i;
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
