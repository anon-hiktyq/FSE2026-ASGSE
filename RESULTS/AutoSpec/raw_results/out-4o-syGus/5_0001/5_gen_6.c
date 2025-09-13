int main()
{
   int x = 0;
   int size;
   int y, z;

   /*@
   loop invariant 0 <= x <= size;
   loop invariant size >= 0;
   loop invariant x == 0 || z >= y;
   loop invariant x > 0 ==> \forall integer i; 0 <= i < x ==> z >= y;
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
