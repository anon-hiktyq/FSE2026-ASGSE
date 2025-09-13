
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant 0 <= x <= 500;
   loop invariant y >= z ==> y == z;
   loop invariant z <= y ==> y == z;
   loop assigns x;
   loop assigns y;
   */
   while(x < 500) {
      x += 1;
      if( z <= y) {
         y = z;
      }
   }


}
