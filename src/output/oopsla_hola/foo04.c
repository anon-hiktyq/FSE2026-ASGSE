
void foo04(int x,int y) {

  x = -50;

  /* >>> LOOP INVARIANT TO FILL <<< */
  
  /*@
    loop invariant y >= 1; 
    loop invariant y >= \at(y, Pre); 
    loop assigns x, y;
  */
  while( x < 0 ) {
    x = x + y;
    y++;
  }

  /*@ assert y > 0;*/
}
