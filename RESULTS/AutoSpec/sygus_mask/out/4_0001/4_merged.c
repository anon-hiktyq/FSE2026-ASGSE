
void foo(int y, int z)
{
   int x = 0;

   /*@
   loop invariant y == z ==> y <= z;
   loop invariant y <= z ==> y == y; // y remains unchanged when z > y;
   loop invariant y <= z ==> y == y; // y remains unchanged if y <= z;
   loop invariant y <= z ==> y == y; // Y remains unchanged if y <= z;
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


}
