
/*@
    requires flag > 0;
    */
    
void foo018(int flag, int a) {
   int b = 0;
   int j = 0;
 
   
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant flag > 0 ==> (j == b);
              loop invariant 0 <= b <= 100;
              loop invariant a == \at(a,Pre);
              loop invariant flag == \at(flag,Pre);
              loop assigns j, b;
            */
            for (b = 0; b < 100 ; ++b){
      if (flag)
         j = j + 1;
   }
            

   /*@ assert flag ==> (j == 100); */
}
