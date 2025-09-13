
int unknown();

void foo013(int flag) {
   int j = 2; 
   int k = 0;

   
   /*@
   loop invariant j == 2 * k + 2 || flag;
   loop invariant flag || j == 2*k + 2;
   loop invariant flag ==> j >= 2;
   loop invariant 1 <= j;
   loop invariant (k > 0 && !flag) ==> j == 2*k + 2;
   loop invariant (j % 2 == 0);
   loop invariant (flag ==> j >= 2);
   loop invariant (flag == 0) ==> (j % 2 == 0);
   loop invariant (!flag) ==> j % 2 == 0;
   loop invariant (!flag || j >= 2);
   loop invariant !flag ==> j == 2 * k + 2;
   loop invariant k == 0 ==> (j % 2 == 0);
   loop invariant j % 2 == 0;
   loop invariant flag || j == 2 * k + 2;
   loop invariant flag || j % 2 == 0;
   loop invariant 2 <= j;
   loop invariant 2 * k + 2 <= j;
   loop invariant 0 <= k;
   loop invariant (k > 0 && !flag) ==> j == 2 * k + 2;
   loop invariant (flag ==> (j >= 2));
   loop invariant !flag || j >= 2;
   loop assigns k;
   loop assigns j;
   */
   while(unknown()){ 
     if (flag)
       j = j + 4;
     else {
       j = j + 2;
       k = k + 1;
     }
   }
   //@ assert (k!= 0 )==> (j == 2 * k + 2 );
}
