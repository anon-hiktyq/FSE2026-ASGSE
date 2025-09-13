
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant z > y ==> y == \old(y);;
   loop invariant z <= y ==> y == z;;
   loop invariant z <= y ==> y == z;
   loop invariant y == z || y > z;
   loop invariant y == \min(z, y);
   loop invariant y <= z;;
   loop invariant y <= z;
   loop invariant x >= 1 ==> y <= z;
   loop invariant x == y + (z <= y ? 500 - z : 0);;
   loop invariant x == \old(x) + (500 - x);
   loop invariant x == \at(x, Pre) + (\by 1 iteration count);
   loop invariant x == 500 ==> y <= z;
   loop invariant x == 0 ==> y == z;
   loop invariant x <= 500;;
   loop invariant \forall integer k; 0 <= k <= x ==> y <= z;
   loop invariant 0 <= x;;
   loop invariant x <= 500;
   loop invariant 0 <= x;
   loop assigns y;
   loop assigns x;
   */
   while(x < 500) {
      x += 1;
      if( z <= y) {
         y = z;
      }
   }

   //post-condition
   // @ assert z >= y;
}
