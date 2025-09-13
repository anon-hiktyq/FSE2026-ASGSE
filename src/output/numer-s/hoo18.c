
/*@
    requires xa + ya > 0;
    */
    
int hoo18(int xa,int ya){

    //pre-condition
   
    //loop-body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (\at(xa,Pre) > 0) ==> (xa + ya == \at(xa,Pre) + \at(ya,Pre));
          loop invariant (\at(xa,Pre) > 0) ==> (xa >= 0);
          loop invariant (\at(xa,Pre) > 0) ==> (ya == \at(ya,Pre) + (\at(xa,Pre) - xa));
          loop invariant (!(\at(xa,Pre) > 0)) ==> ((ya == \at(ya,Pre))&&(xa == \at(xa,Pre)));
          loop assigns xa, ya;
            */
            while (xa > 0) {
        xa--;
        ya++;
    }
            

    //post-condition
    /*@ assert ya >= 0; */
}
