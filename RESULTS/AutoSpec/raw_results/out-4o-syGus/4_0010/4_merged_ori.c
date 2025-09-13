
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant z >= y || x == 0;
   loop invariant z > y ==> y == \old(y);
   loop invariant z <= y ==> y == z;
   loop invariant y == z || y != z;
   loop invariant y <= z;
   loop invariant x > 0 ==> y <= \old(y);
   loop invariant x > 0 ==> (z <= \old(y) ==> y == z);
   loop invariant x == \old(x) + 1;
   loop invariant x == \at(x, Pre) + (\at(x, Pre) < 500 ? x : 500);
   loop invariant x == 1 || y == z;
   loop invariant x == 0 ==> y == \old(y);
   loop invariant x < 501;
   loop invariant \old(x) <= x;
   loop invariant \forall integer k; 0 <= k < x ==> z >= y;
   loop invariant \forall integer k; 0 <= k < x ==> y <= z;
   loop invariant \forall integer k; 0 <= k < x ==> (z <= y ==> y == z);
   loop invariant \exists integer k; 0 <= k <= x ==> y == z || y >= z;
   loop invariant (y == z) || (y > z);
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
