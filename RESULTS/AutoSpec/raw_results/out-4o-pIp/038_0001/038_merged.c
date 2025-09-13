

void foo038(int n) {
  int x=0;
  int y=0;
  int i=0;
  
 
  /*@
  loop invariant y == x / 2;
  loop invariant y <= x/2;
  loop invariant y <= x / 2;
  loop invariant x == i;
  loop invariant x == 2*y || x == 2*y + 1;
  loop invariant i % 2 == 1 ==> x == 2 * y + 1;
  loop invariant i % 2 == 0 ==> x == 2*y;
  loop invariant i % 2 == 0 ==> x == 2 * y;
  loop invariant \forall integer k; 0 <= k < i ==> (k % 2 == 0 ==> y >= k / 2);
  loop invariant 2 * y <= i;
  loop invariant 0 <= i;
  loop invariant (x == i) && (y <= x/2);
  loop assigns y;
  loop assigns x;
  loop assigns i;
  */
  while(i<n) {
    i++;
    x++;
    if(i%2 == 0) y++;
  }
  
 //@ assert (i%2 == 0) ==> (x==2*y);
}
