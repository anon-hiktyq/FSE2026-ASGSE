
int unknown();

void foo013(int flag) {
   int j = 2; 
   int k = 0;

   
   /*@
   loop invariant k >= 0;
   loop invariant j == 2 * k + 2 || j == 2 * k + 4;
   loop invariant flag ==> j % 2 == 0;
   loop assigns j;
   loop assigns k;
   */
   while(unknown()){ 
     if (flag)
       j = j + 4;
     else {
       j = j + 2;
       k = k + 1;
     }
   }
   // @ assert (k!= 0 )==> (j == 2 * k + 2 );
}
