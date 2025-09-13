

void foo034(int n) {
  int x=0;
  int y=0;
  int i=0;
  int m=10;
  
 
  /*@
  loop invariant 0 <= i <= n;
  loop invariant x == i;
  loop invariant y <= x/2;
  loop invariant i % 2 == 0 ==> y == i / 2;
  loop invariant i % 2 == 1 ==> y == (i - 1) / 2;
  loop assigns i;
  loop assigns x;
  loop assigns y;
  */
  while(i < n) {
    i++;
    x++;
    if(i%2 == 0) y++;
  }
  
  // @ assert (i == m) ==> (x == 2* y);*/
}

