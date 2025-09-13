
/*@
    requires a >= 0;
  requires b >= 0;
    */
    
int hoo37(int a, int b) {
    
    int product = 0;  
    int i = 0;        

    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (0 < \at(b,Pre)) ==> (product == a * i) ;
          loop invariant (0 < \at(b,Pre)) ==> (0 <= i <= b) ;
          loop invariant (!(0 < \at(b,Pre))) ==> ((i == 0)&&(product == 0)&&(b == \at(b,Pre))&&(a == \at(a,Pre)));
          loop invariant b == \at(b,Pre);
          loop invariant a == \at(a,Pre);
          loop assigns product, i;
            */
            while (i < b) {
        product = product + a;  
        i = i + 1;
    }
            

    
    /*@ assert product == a * b; */
}
