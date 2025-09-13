
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant x == 500 - (y - z);  
   loop invariant y <= z;  
   loop invariant z >= y;  
   loop invariant z - y >= 0;
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
