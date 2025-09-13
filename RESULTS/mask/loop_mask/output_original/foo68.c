
void foo68(int n)
{
  int x=0;
  int y=0;
  int i=0;
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
        /*@
          loop invariant (0 < \at(n,Pre)) ==> (x == i);
          loop invariant (0 < \at(n,Pre)) ==> (y == i / 2);
          loop invariant (0 < \at(n,Pre)) ==> (0 <= i <= n);
          loop invariant (!(0 < \at(n,Pre))) ==> ((i == 0) && (y == 0) && (x == 0) && (n == \at(n,Pre)));
          loop invariant n == \at(n,Pre);
          loop assigns i, x, y;
          loop variant n - i;
        */
        while(i<n) {
          i++;
          x++;
          if(i%2 == 0) y++;
        }
            
  
 /* mask_1 */
}
