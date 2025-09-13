
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant z > y ==> y == y;
   loop invariant z <= y ==> y == z;
   loop invariant y == z || y < z;
   loop invariant y == z ==> \forall integer k; 0 <= k <= x ==> y == z;
   loop invariant y <= z;
   loop invariant x > 0 ==> y <= \old(y);
   loop invariant x == \old(y) && y <=> y;
   loop invariant x == \old(x) + (\old(500-x));
   loop invariant x == \at(x, Pre) + 1;
   loop invariant x == 500 ==> y <= z;
   loop invariant x == 0 || y >= z;
   loop invariant x == 0 ==> y == \old(y);
   loop invariant x == (x - y);
   loop invariant \forall integer k; 0 <= k <= 500 ==> x <= 500;
   loop invariant \forall integer k; 0 <= k < x ==> y <= z;
   loop invariant \exists integer k; 0 <= k <= x && y == z;
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
