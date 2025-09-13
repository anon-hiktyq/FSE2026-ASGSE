int main()
{
   int x = 0;
   int size;
   int y, z;

   /*@
   loop invariant 0 <= x <= size;
   loop invariant \forall integer k; 0 <= k < x ==> (z <= y ==> y == z);
   loop invariant z <= y || x == 0;
   loop assigns x;
   loop assigns y;
   */
   while(x < size) {
      x += 1;
      if( z <= y) {
         y = z;
      }
   }


}
