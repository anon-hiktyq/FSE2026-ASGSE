
/*@
    requires n > 0;
    */
    
int hoo36(int n) {
    
    int sum = 0;   
    int i = 1;     

    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (1 <= \at(n,Pre)) ==> (sum == (i - 1) * i / 2) ;
          loop invariant (1 <= \at(n,Pre)) ==> (1 <= i <= \at(n,Pre) + 1) ;
          loop invariant (!(1 <= \at(n,Pre))) ==> ((i == 1)&&(sum == 0)&&(n == \at(n,Pre)));
          loop invariant n == \at(n,Pre);
          loop assigns sum, i;
            */
            while (i <= n) {
        sum = sum + i;  
        i = i + 1;      
    }
            

    
    
    /*@ assert sum == (n * (n + 1)) / 2; */
}
