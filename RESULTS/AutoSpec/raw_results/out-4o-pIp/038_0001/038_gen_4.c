

void foo038(int n) {
  int x=0;
  int y=0;
  int i=0;
  
 
  /*@
  loop invariant 0 <= i <= n;
  loop invariant x == i;
  loop invariant y == x / 2;
  loop invariant 2 * y <= i;
  loop assigns i, x, y;
  */
  while(i<n) {
    i++;
    x++;
    if(i%2 == 0) y++;
  }
  
 // @ assert (i%2 == 0) ==> (x==2*y);
}
