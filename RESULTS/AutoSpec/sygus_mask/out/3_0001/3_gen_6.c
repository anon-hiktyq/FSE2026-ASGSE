
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant 0 <= x <= 5;
   loop invariant y <= z ==> y == z;
   loop invariant \forall integer k; 0 <= k < x ==> (z <= y ==> y == z);
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
