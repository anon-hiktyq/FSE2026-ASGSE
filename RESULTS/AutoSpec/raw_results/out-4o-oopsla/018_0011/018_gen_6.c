
/*@
requires flag > 0;
*/
void foo018(int flag, int a) {
   int b = 0;
   int j = 0;
 
   /*@
   loop invariant 0 <= b <= 100;
   loop invariant flag > 0 ==> j == b;
   loop invariant \forall integer k; 0 <= k < b ==> (flag > 0 ==> j == k+1);
   loop assigns b;
   loop assigns j;
   */
   for (b = 0; b < 100 ; ++b){
      if (flag)
         j = j + 1;
   }

   // @ assert falg ==> (j == 100);
}