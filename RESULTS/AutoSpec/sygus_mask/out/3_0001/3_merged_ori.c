
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant z > y ==> y remains unchanged;
   loop invariant z <= y ==> y == z;
   loop invariant y >= z ==> y == z;
   loop invariant y == z || y > z;
   loop invariant y <= z ==> y == z;
   loop invariant y <= z ==> y == y;
   loop invariant y <= z ==> \forall integer k; 0 <= k < x ==> y == z;
   loop invariant x == 0 ==> (y == y);
   loop invariant x <= 5;
   loop invariant \forall integer k; 0 <= k < x ==> (z <= y ==> y == z);
   loop invariant 0 <= x;
   loop invariant (z <= y) ==> (y == z);
   loop assigns y;
   loop assigns x;
   */
   while(x < 5) {
      x += 1;
      if( z <= y) {
         y = z;
      }
   }


}
