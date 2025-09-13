
void foo042(int flag) {
  int x = 1;
  int y = 1;
  int a;

  if (flag)
    a = 0;
  else
    a = 1;

  
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant 0 <= x;
          loop invariant 0 <= y;
          loop invariant flag == \at(flag,Pre);
          loop invariant a % 2 == (flag ? (x + y) % 2 : (x + y + 1) % 2); // This invariant is retained
          loop assigns x, y, a;
            */
            while (unknown()) {
    if (flag) {
      a = x + y;
      x++;
    } else {
      a = x + y + 1;
      y++;
    }
    if (a % 2 == 1)
      y++;
    else
      x++;
  }
            
  
  if (flag){
    a++;
  }
  /*@ assert a % 2 == 1; */
}
