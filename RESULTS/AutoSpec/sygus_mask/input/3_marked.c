
/* 2. FUNC CONTRACT */
void foo(int y, int z)
{
   int x = 0;

   /* 1. LOOP INVARIANT */
   while(x < 5) {
      x += 1;
      if( z <= y) {
         y = z;
      }
   }


}
