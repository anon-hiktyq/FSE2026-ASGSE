
int unknown1();
int unknown2();


void foo025() {
  int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

 
  /*@
  loop invariant y <= x;
  loop invariant y <= x + 1;
  loop invariant y - j <= x;
  loop invariant y - 1 <= x;
  loop invariant x >= 0 && y >= 0;
  loop invariant x == y || y == x + 1;
  loop invariant x == y || x == y + 1;
  loop invariant x == y || x + 1 == y;
  loop invariant x == y ==> i >= j;
  loop invariant x == y + (i - j);
  loop invariant x <= y;
  loop invariant x <= y + i - j;
  loop invariant x <= y + 1;
  loop invariant x <= y + (i - j);
  loop invariant x != y ==> i < j;
  loop invariant j <= i;
  loop invariant j <= 2*i;
  loop invariant i >= j || y == x + 1;
  loop invariant i >= j || j > i;
  loop invariant i >= j || i == j;
  loop invariant i >= j || i < j;
  loop invariant i >= j ==> x == y;
  loop invariant i >= 0 && j >= 0;
  loop invariant i + j <= x + y;
  loop invariant \forall integer n; 0 <= n <= x ==> x >= y - j;
  loop invariant \forall integer n; 0 <= n <= j ==> x >= y - n;
  loop invariant \forall integer n; 0 <= n <= i ==> x >= y - j;
  loop invariant \forall integer n; 0 <= n < i ==> x == y || x == y + 1;
  loop invariant \forall integer n; 0 <= n < i ==> x == y + (i - j);
  loop invariant \forall integer m; 0 <= m < y ==> x == y || y == x + 1;
  loop invariant \forall integer m; 0 <= m < x ==> i >= j;
  loop invariant \forall integer k; 0 <= k <= y ==> (x == y) || (x > y);
  loop invariant \forall integer k; 0 <= k <= j ==> y >= x;
  loop invariant \forall integer k; 0 <= k <= j ==> y >= x || x > y;
  loop invariant \forall integer k; 0 <= k <= j ==> x >= y - 1;
  loop invariant \forall integer k; 0 <= k <= i ==> x >= y;
  loop invariant \forall integer k; 0 <= k <= i ==> x >= y || y > x;
  loop invariant \forall integer k; 0 <= k <= i ==> x >= y - j;
  loop invariant \forall integer k; 0 <= k <= i ==> x <= y + 1;
  loop invariant \exists integer k; 0 <= k <= i ==> x + y >= 2*k;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= x + y;
  loop invariant (i >= j) ==> x == y;
  loop invariant 0 <= x && 0 <= y;
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
    loop invariant y <= x;
    loop invariant x == y || y == x + 1;
    loop invariant x == y ==> i >= j;
    loop invariant x <= y;
    loop invariant x <= y + 1;
    loop invariant j <= x + y;
    loop invariant j <= i;
    loop invariant i >= j || j > i;
    loop invariant i >= j || i == j;
    loop invariant i >= j ==> x == y;
    loop invariant i >= 0 && j >= 0;
    loop invariant i <= x + y;
    loop invariant i + j <= x + y;
    loop invariant \forall integer n; 0 <= n <= i ==> x >= y - j;
    loop invariant \forall integer k; 0 <= k <= y ==> k <= x + y;
    loop invariant \forall integer k; 0 <= k <= j ==> y >= x || x > y;
    loop invariant \forall integer k; 0 <= k <= i ==> x >= y || y > x;
    loop invariant \forall integer k; 0 <= k <= i ==> x == y;
    loop invariant \forall integer k; 0 <= k <= i ==> k <= j + i;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant 0 <= x || 0 <= y;
    loop invariant 0 <= x && 0 <= y;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop invariant 0 <= i || 0 <= j;
    loop invariant 0 <= i && 0 <= j;
    loop invariant (x == y ==> i >= j);
    loop invariant (x != y ==> i < j);
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
