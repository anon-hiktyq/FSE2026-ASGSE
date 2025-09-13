
/*@
    requires flag > 0;
*/
void foo59(int flag, int a) {
   int b = 0;
   int j = 0;

   /*@
      loop invariant 0 <= b <= 100;
      loop invariant flag ==> j == b;
      loop invariant a == \at(a,Pre);
      loop invariant flag == \at(flag,Pre);
      loop assigns j, b;
      loop variant 100 - b;
   */
   for (b = 0; b < 100; ++b) {
      if (flag)
         j = j + 1;
   }

   /*@ assert flag ==> (j == 100); */
}
