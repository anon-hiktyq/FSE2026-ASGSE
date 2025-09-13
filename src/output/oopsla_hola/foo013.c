
void foo013(int flag) {
   int j = 2; 
   int k = 0;

   /*@
   loop invariant j >= 2 + 2 * k;
   loop invariant k >= 0;
   loop invariant flag == \at(flag,Pre);
   loop assigns j, k;
   */
   while(unknown()){ 
     if (flag)
       j = j + 4;
     else {
       j = j + 2;
       k = k + 1;
     }
   }
            
   /*@ assert (k != 0) ==> (j >= 2 + 2 * k); */
}
