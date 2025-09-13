int main()
{
   int x = 0;
   int size;
   int y, z;

   /*@
   loop invariant 0 <= x <= size;
   loop invariant size > 0 ==> z >= y;
   loop invariant size <= 0 ==> true;
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

   //post-condition
   if(size > 0) {
      // @ assert z >= y;
   }
}
