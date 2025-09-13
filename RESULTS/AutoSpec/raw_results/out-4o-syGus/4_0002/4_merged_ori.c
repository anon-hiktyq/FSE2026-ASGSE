
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant z > y ==> \forall integer k; 0 <= k < x ==> z > y;;
   loop invariant z <= y ==> y == z;
   loop invariant z <= y ==> x < 500;;
   loop invariant y == z || y > z;;
   loop invariant y == \min(\at(y, Pre), z);
   loop invariant y <= z;
   loop invariant x > 0 ==> z >= y;
   loop invariant x > 0 ==> y <= \old(y);
   loop invariant x == \old(x) + 1 * (\at(x, Pre) == 0);
   loop invariant x == \at(x, Pre) + (\at(x, Here) - \at(x, Pre));
   loop invariant x == 500 ==> z >= y;;
   loop invariant x == 500 ==> y == \old(y) || y == z;
   loop invariant x == 0 || y == z;
   loop invariant x == 0 ==> y == \old(y);
   loop invariant x <= 500;;
   loop invariant x <= 500 ==> z >= y;
   loop invariant x <= 500 && x >= 0;
   loop invariant \forall integer k; 0 <= k <= x ==> y <= z;
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
