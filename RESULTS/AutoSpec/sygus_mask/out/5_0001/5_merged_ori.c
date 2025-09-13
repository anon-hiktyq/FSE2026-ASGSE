int main()
{
   int x = 0;
   int size;
   int y, z;

   /*@
   loop invariant z; <= y;
   loop invariant z <= y || x == 0;
   loop invariant z <= y ==> y == z;;
   loop invariant z <= y ==> y == z;
   loop invariant y == z ==> y <= z;
   loop invariant y == \max(z, \old(y));
   loop invariant x <= size;
   loop invariant \forall integer k; 0 <= k < x ==> z <= y;
   loop invariant \forall integer k; 0 <= k < x ==> (z <= y ==> y >= z);
   loop invariant \forall integer k; 0 <= k < x ==> (z <= y ==> y == z);
   loop invariant 0 <= x;
   loop invariant (x == size) ==> (y == z);
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
