
/*@
requires flag > 0;
*/
void foo018(int flag, int a) {
   int b = 0;
   int j = 0;
 
   /*@
   loop invariant 0 <= b <= 100;
   loop invariant 0 <= j <= 100;
   loop invariant b <= 100;
   loop invariant \forall integer k; 0 <= k < b ==> j >= k;
   loop invariant \forall integer k; 0 <= k < b ==> j >= k || flag == 0;
   loop invariant j <= b;
   loop invariant flag > 0 ==> j == b;
   loop invariant flag > 0 && j <= 100 && b <= 100;
   loop invariant b == 100 ==> (flag > 0 ==> j == 100);
   loop invariant j == b || !flag;
   loop invariant j == 0 || flag > 0;
   loop invariant j <= b;
   loop invariant j <= 100;
   loop invariant j <= 100 || b <= 100;
   loop invariant flag > 0 || j == 0;
   loop invariant flag > 0 ==> j == b;
   loop invariant flag > 0 ==> j == b >= 0;
   loop invariant flag > 0 ==> j == b <= 100;
   loop invariant flag > 0 ==> j <= b;
   loop invariant flag > 0 ==> j <= b <= 100;
   loop invariant flag > 0 ==> j <= 100;
   loop invariant flag > 0 ==> b == j;
   loop invariant flag > 0 ==> b == j <= 100;
   loop invariant flag > 0 ==> 0 <= j <= 100;
   loop invariant flag > 0 ==> (j == b);
   loop invariant flag > 0 && j == b;
   loop invariant flag > 0 && j <= b;
   loop invariant flag > 0 && 0 <= j <= 100;
   loop invariant flag ==> j == b;
   loop invariant flag ==> (j == b);
   loop invariant flag <= 0 || j <= 100;
   loop invariant flag <= 0 ==> j == 0;
   loop invariant flag && b == 100 ==> j == b;
   loop invariant b == j;
   loop invariant b == j || j == 0;
   loop invariant b == j || flag == 0;
   loop invariant b == j || !flag;
   loop invariant b == j && 0 <= j <= 100;
   loop invariant b == 0 || b > 0;
   loop invariant b <= j || flag <= 0;
   loop invariant b <= j || !flag;
   loop invariant b <= 100;
   loop invariant b - j == 100 - 100;
   loop invariant b - j == 0 || flag == 0;
   loop invariant \forall integer k; 0 <= k < b ==> k < 100;
   loop invariant \forall integer k; 0 <= k < b ==> flag > 0 ==> k < j;
   loop invariant \forall integer k; 0 <= k < b ==> flag > 0 && j > 0;
   loop invariant \forall integer k; 0 <= k < b ==> flag ==> k < j;
   loop invariant \forall integer k; 0 <= k < b ==> flag ==> j > k;
   loop invariant \forall integer k; 0 <= k < b ==> flag == 0 ==> j == 0;
   loop invariant \forall integer k; 0 <= k < b ==> flag <= 0 ==> j == 0;
   loop invariant \forall integer k; 0 <= k < b ==> flag && k < j;
   loop invariant \forall integer k; 0 <= k < b ==> (flag || j == 0);
   loop invariant \forall integer k; 0 <= k < b ==> !flag ==> j == 0;
   loop invariant \exists integer k; 0 <= k <= b < 100 ==> j == k;
   loop invariant 0 <= j;
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