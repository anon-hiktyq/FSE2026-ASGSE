int main()
{
   int x = 0;
   int size;
   int y, z;

   /*@
   loop invariant z <= y;
   loop invariant z <= y || x == 0;
   loop invariant z <= y || \forall integer k; 0 <= k < x ==> z > y;
   loop invariant z <= y ==> y == z;
   loop invariant x <= size;
   loop invariant \forall integer k; 0 <= k < x ==> z <= y ==> y == z;
   loop invariant \forall integer k; 0 <= k < x ==> (z > y ==> y remains unchanged);
   loop invariant \forall integer k; 0 <= k < x ==> (z <= y ==> y == z);
   loop invariant \exists integer k; 0 <= k < x ==> (z <= y ==> y == z);
   loop invariant 0 <= x;
   loop invariant (z > y) ==> (y remains unchanged);
   loop invariant (z <= y) ==> (y == z);
   loop invariant (z <= y) ==> (y == z || y <= z);
   loop assigns y;
   loop assigns x;
   */
   while(x < size) {
      x += 1;
      if( z <= y) {
         y = z;
      }
   }


}
