
/*@
    requires x <= A-1;
    */
    
int test(int A,int x) {

        /* >>> LOOP INVARIANT TO FILL <<< */
        
        /*@
          loop invariant x <= A-1;
          loop invariant A == \at(A,Pre);
        */
        while (x < 0)  {
            x = x + A;
        }
               
    /*@ assert x <= A -1; */
    return x;
}
