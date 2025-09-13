
/*@
requires flag > 0;
*/
void foo018(int flag, int a) {
   int b = 0;
   int j = 0;
 
   /*@
   loop invariant 0 <= b <= 100;
   loop invariant 0 <= j <= 100;
   loop invariant flag > 0 ==> j == b;
   loop invariant j <= 100 * flag;
   loop invariant \forall integer k; 0 <= k < b ==> flag > 0 ==> j == k + 1;
   loop invariant \forall integer k; 0 <= k < b ==> j <= 100 * flag;
   loop invariant j == b;
   loop invariant j <= b;
   loop invariant j <= 100;
   loop invariant j <= 100 * flag;
   loop invariant flag > 0 ==> j == b;
   loop invariant flag > 0 ==> j <= 100;
   loop invariant flag > 0 ==> b == j;
   loop invariant flag > 0 ==> (j == b);
   loop invariant flag > 0 ==> (b <= 100 && j <= 100);
   loop invariant flag ==> j == b;
   loop invariant flag ==> (j == b);
   loop invariant flag == 1 || flag != 0;
   loop invariant flag == 0 ==> j == 0;
   loop invariant flag <= 0 ==> j == 0;
   loop invariant b == j;
   loop invariant b == j || b == j + 1;
   loop invariant b <= 100;
   loop invariant 0 <= j;
   loop invariant 0 <= b;
   loop invariant 0 < flag;
   loop assigns j;
   loop assigns b;
   */
   for (b = 0; b < 100 ; ++b){
      if (flag)
         j = j + 1;
   }

   // @ assert falg ==> (j == 100);
}