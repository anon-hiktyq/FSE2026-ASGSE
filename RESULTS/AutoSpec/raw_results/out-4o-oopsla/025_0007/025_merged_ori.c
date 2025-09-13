
int unknown1();
int unknown2();


void foo025() {
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

 
  /*@
  loop invariant x <= y;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop assigns y;
  loop assigns x;
  loop assigns j;
  loop assigns i;
  */
  while(unknown1())
  {
    
    /*@
    loop invariant x == y ==> i >= j;
    loop invariant x <= y && y >= 0;
    loop invariant x + y == i + j + y;
    loop invariant x + j == y + i;
    loop invariant x + j <= y + i;
    loop invariant j <= y;
    loop invariant j <= i;
    loop invariant i >= j || j > i;
    loop invariant i >= j ==> x == y;
    loop invariant i <= x;
    loop invariant i + j == x + y;
    loop invariant i + j == x + y - 1;
    loop invariant \forall integer k; 0 <= k <= i ==> x <= y;
    loop invariant \forall integer k; 0 <= k <= i ==> x + y >= k;
    loop invariant \forall integer k; 0 <= k < j ==> x != y;
    loop invariant \forall integer k; 0 <= k < i ==> x == y;
    loop invariant \exists integer k; 0 <= k <= i && k <= j;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant 0 <= i && 0 <= j;
    loop invariant x <= y;
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
