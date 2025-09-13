
int hoo16(){
    int x = 0;
    int y = 0;
    int z = 0;

   
    //loop-body
    
            
        /*@
            loop invariant x >= 0;
            loop invariant y >= 0;
            loop invariant z % 2 == 0;
            loop invariant x + y + z == 0;
            loop assigns x, y, z;
        */
            while (x > 0) {
        x++;
        y++;
        z -= 2;
    }
            

    //post-condition
    /*@ assert x + y + z == 0; */
}
