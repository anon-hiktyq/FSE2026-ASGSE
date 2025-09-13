
int unknown1();
int unknown2();


void foo025() {
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

 
  /*@
  loop invariant x >= y;
  loop invariant x == y || x == y + 1;
  loop invariant x == y ==> i >= j;
  loop invariant x != y ==> i <= j;
  loop invariant j <= i;
  loop invariant i >= 0 && j >= 0;
  loop invariant \forall integer k; x == y ==> (i >= j);
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop assigns x, y, i, j;
  */
  while(unknown1())
  {
    
    /*@
    loop invariant y <= x;
    loop invariant x == y || x == y + 1;
    loop invariant x == y ==> i >= j;
    loop invariant x != y ==> i <= j;
    loop invariant j <= i;
    loop invariant i >= 0 && j >= 0;
    loop invariant \forall integer k; x == y ==> (i >= j);
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
