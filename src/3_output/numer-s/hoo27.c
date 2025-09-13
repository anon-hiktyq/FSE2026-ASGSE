
/*@
    requires x >= 0;
    requires y >= 1;
    */
    
int hoo27(int x,int y) {
    int q = 0;
    int a = 0;
    int b = x;

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (\at(x,Pre) != 0) ==> (q * y + a + b == \at(x,Pre));
          loop invariant (\at(x,Pre) != 0) ==> (0 <= a < y);
          loop invariant (\at(x,Pre) != 0) ==> (b >= 0);
          loop invariant (!(\at(x,Pre) != 0)) ==> ((b == \at(x,Pre))&&(a == 0)&&(q == 0)&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
          loop invariant y == \at(y,Pre);
          loop invariant x == \at(x,Pre);
          loop assigns q, a, b;
            */
            while(b != 0) {
        if (a + 1 == y) {
            q = q + 1;
            a = 0;
            b = b - 1;
        }
        else {
            a = a + 1;
            b = b - 1;
        }
    }
            

    /*@ assert q * y + a + b == x; */
}
