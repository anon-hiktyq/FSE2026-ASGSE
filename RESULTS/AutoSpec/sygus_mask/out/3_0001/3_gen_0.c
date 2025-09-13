
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant 0 <= x <= 5;
   loop invariant (z <= y) ==> (y == z);
   loop invariant x == 0 ==> (y == y);
   loop assigns x;
   loop assigns y;
   */
   while(x < 5) {
      x += 1;
      if( z <= y) {
         y = z;
      }
   }


}
