int main()
{
   int x = 0;
   int size;
   int y, z;

   /*@
   loop invariant 0 <= x <= size;
   loop invariant size >= 0;
   loop invariant x == \at(x, Pre) + (\forall integer k; 0 <= k < x);
   loop invariant \forall integer k; 0 <= k < x ==> (z >= y || y == z);
   loop assigns x, y;
   */
   while(x < size) {
      x += 1;
      if( z <= y) {
         y = z;
      }
   }

   //post-condition
   if(size > 0) {
      // @ assert z >= y;
   }
}
