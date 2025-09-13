
/*@
    requires n > 0;
    */
    
void foo46(int n) {

    int c = 0;

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant  (\at(n, Pre) > 0) ==> (c != n ==> c <= n);
          loop invariant  (\at(n, Pre) > 0) ==> (((c == 0) && (n == \at(n, Pre))) || (c >= 0 && c <= n));
          loop invariant (\at(n, Pre) > 0) ==> (n == \at(n, Pre));
          loop assigns c;
            */
            while (unknown()) {
        {
          if (unknown()) {
            if (c != n) {
                c = c + 1;
            }
          } else {
            if (c == n) 
            {
                c = 1;
            }
          }
    
        }
    
    }
               
    /*@ assert  (c != n) ==> (c <= n); */
    

  

}
