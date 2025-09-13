int main()
{
   int x = 0;
   int size;
   int y, z;

   /*@
   loop invariant 0 <= x <= size;
   loop invariant z <= y ==> y == z; 
   loop invariant y >= z; 
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
