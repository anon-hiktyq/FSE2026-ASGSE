
void foo67(int n,int y) {
    
    int x = 1;

    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant (1 <= \at(n,Pre)) ==> (1 <= x && x <= n + 1);
            loop invariant n == \at(n,Pre); // Ensured n is constant
            loop assigns y, x;
            */
            while (x <= n) {
        y = n - x;
        x = x + 1;
    }
            

    /*@ assert (n > 0) ==> (y >= 0); */


}
