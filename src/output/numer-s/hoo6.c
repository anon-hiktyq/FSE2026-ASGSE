
/*@
    requires x > 0;
    requires y > 0;
    requires z > 0;
    requires w > 0;
    */
    
int hoo6(int a,int w,int x,int y,int z) {

    //pre-condition
    x = w;
    z = x + 1;
    y = w + 1;


    //loop-body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            axiomatic N {
                logic int n; // Declare n as a logic variable
            }
            loop invariant y - z == -1; // y is always one less than z
            loop invariant y == \at(w, Pre) + 1 + n; // where n is the number of iterations
            loop invariant z == \at(w, Pre) + 2 + n; // where n is the number of iterations
            loop invariant x == \at(w, Pre);
            loop invariant w == \at(w, Pre);
            loop invariant a == \at(a, Pre);
            loop assigns y, z;
            */
            while (unknown()) {
        y = y + 1;
        z = z + 1;
    }
            

    //post-conditon
    /*@ assert y == z; */
}
