
int unknown1();
int unknown2();


void foo025() {
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

 
  /*@
  loop invariant x <= y;
  loop invariant x - y <= 0;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant 0 <= i + j;
  loop assigns y;
  loop assigns x;
  loop assigns j;
  loop assigns i;
  */
  while(unknown1())
  {
    
    /*@
    loop invariant y == x + i + j;
    loop invariant x - y <= 0;
    loop invariant x + j <= y + i;
    loop invariant j <= i;
    loop invariant i - j == x - y;
    loop invariant i + j == x + y;
    loop invariant i + j <= y;
    loop invariant \forall integer k; 0 <= k <= j ==> j >= 0;
    loop invariant \forall integer k; 0 <= k <= i + j ==> x <= y;
    loop invariant \forall integer k; 0 <= k < i ==> x <= y;
    loop invariant \forall integer k; 0 <= k < i ==> x + k <= y;
    loop invariant 0 <= y - i;
    loop invariant 0 <= x + y;
    loop invariant 0 <= x + j;
    loop invariant (x == y) ==> (i >= j);
    loop invariant x <= y;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop invariant 0 <= i + j;
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
