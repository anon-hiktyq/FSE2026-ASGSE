
/*@
requires flag > 0;
*/
void foo018(int flag, int a) {
   int b = 0;
   int j = 0;
 
   /*@
   loop invariant b <= j;
   loop invariant j <= 100;
   loop invariant \forall integer i; 0 <= i < b ==> j == i + 1;
   loop invariant \forall integer i; 0 <= i < b ==> flag != 0;
   loop invariant b == 0 ==> j == 0;
   loop invariant flag != 0 ==> j == b;
   loop assigns j, b;
   loop invariant j == b;
   loop invariant j == b && flag > 0;
   loop invariant flag > 0 ==> j == b;
   loop invariant flag ==> j == b;
   loop invariant flag ==> (j == b);
   loop invariant flag <= 0 ==> j == 0;
   loop invariant flag && 0 <= b <= 100 ==> j == b;
   loop invariant b <= 100;
   loop invariant 0 <= b;
   loop invariant 0 < flag;
   loop invariant !flag ==> j == 0;
   loop assigns j;
   loop assigns b;
   */
   for (b = 0; b < 100 ; ++b){
      if (flag)
         j = j + 1;
   }

   // @ assert falg ==> (j == 100);
}