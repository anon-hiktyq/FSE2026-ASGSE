
int unknown1();
int unknown2();


void foo025() {
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

 
  /*@
  loop invariant y; <= x;
  loop invariant y <= x;
  loop invariant y <= x + 1;
  loop invariant x <= y;
  loop invariant j; <= i;
  loop invariant j <= i;
  loop invariant 0 <= y;;
  loop invariant 0 <= y;
  loop invariant 0 <= x;;
  loop invariant 0 <= x;
  loop invariant 0 <= j;;
  loop invariant 0 <= j;
  loop invariant 0 <= i;;
  loop invariant 0 <= i;
  loop assigns y;
  loop assigns x;
  loop assigns j;
  loop assigns i;
  */
  while(unknown1())
  {
    
    /*@
    loop invariant y <= x;
    loop invariant x <= y;
    loop invariant j <= i;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
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
