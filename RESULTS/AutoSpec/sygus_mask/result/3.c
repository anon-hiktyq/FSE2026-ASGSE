
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant y <= z ==> y == y;
   loop invariant x == 0 ==> (y == y);
   loop invariant x <= 5;
   loop invariant \forall integer k; 0 <= k < x ==> (z <= y ==> y == z);
   loop invariant 0 <= x;
   loop assigns y;
   loop assigns x;
   */
   while(x < 5) {
      x += 1;
      if( z <= y) {
         y = z;
      }
   }
//post-condition
   //@assert(z >= y);
}