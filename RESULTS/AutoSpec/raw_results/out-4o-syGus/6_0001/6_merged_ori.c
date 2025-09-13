int main()
{
   int x = 0;
   int size;
   int y, z;

   /*@
   loop invariant z <= y || x == 0;
   loop invariant y <= z;
   loop invariant x == 0 || z >= y;
   loop invariant x == 0 || (x < size ==> z >= y);
   loop invariant x <= size;
   loop invariant x <= size && (x > 0 ==> z >= y);
   loop invariant size > 0 ==> z >= y;
   loop invariant size <= 0 ==> true;
   loop invariant \forall integer k; 0 <= k < x ==> z >= y;
   loop invariant \forall integer k; 0 <= k < x ==> z <= y;
   loop invariant \forall integer i; 0 <= i < x ==> z >= y;
   loop invariant 0 <= x;
   loop assigns y;
   loop assigns x;
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
