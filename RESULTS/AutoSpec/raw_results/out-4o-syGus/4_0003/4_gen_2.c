
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant 0 <= x <= 500;
   loop invariant z >= y;
   loop invariant x <= 500;
   loop assigns x;
   loop assigns y;
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
