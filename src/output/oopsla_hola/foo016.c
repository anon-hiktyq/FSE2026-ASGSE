
void foo016(int i, int j) {
  
  int x = i;
  int y = j;
 
  /*@
    loop invariant (i != 0) ==> (x <= \at(i, Pre)); 
    loop invariant (i != 0) ==> (y == \at(j, Pre) - (\at(i, Pre) - x));
    loop invariant !(i != 0) ==> (y == \at(j, Pre) && x == \at(i, Pre) && j == \at(j, Pre) && i == \at(i, Pre));
    loop invariant j == \at(j, Pre);
    loop invariant i == \at(i, Pre);
    loop assigns x, y;
  */
  while(x != 0) {
    x--;
    y--;
  }
  
  /*@ assert (i == j) ==> (y == 0);*/
}
