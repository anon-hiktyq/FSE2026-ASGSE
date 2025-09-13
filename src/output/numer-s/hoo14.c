
/*@
    requires k >= 0;
    requires k <= 1;
    */
    
int hoo14(int k){
    int i = 1;
    int j = 1;

    //pre-condition
    //@ assert \at(k,Pre) >= 0 && \at(k,Pre) <= 1 && (j == 1) && (i == 1) && (k == \at(k,Pre));
    
    //loop-body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant k == \at(k, Pre) - (i - 1);
            loop invariant i >= 1;
            loop invariant j == 1 + (\at(k, Pre) * (i - 1) - (i - 1) * (i - 2) / 2);
            loop assigns i, j, k;
            */
            while (unknown()) {
        i = i + 1;
        j = j + k;
        k = k - 1;
    }
            

    //post-condition
    /*@ assert i >= 1; */
}
