
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant 0 <= x <= 5;
   loop invariant z >= y;
   loop invariant \forall integer k; 0 <= k < x ==> y == z || y <= z;
   loop assigns x, y;
   */
   while(x < 5) {
      x += 1;
      if( z <= y) {
         y = z;
      }
   }

   //post-condition
   // @ assert z >= y;
}
