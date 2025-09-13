
void foo011() {
  int j = 0;
  int i = 0;
  int x = 100;
   
  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant j == 2 * i;
              loop invariant 0 <= i <= x;
              loop invariant x == 100;
              loop assigns j, i;
            */
            for (i = 0; i < x ; i++){
    j = j + 2;
  }
            

  /*@ assert j == 2*x; */
}
