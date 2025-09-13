
void foo92(int z1,int z2,int z3) {

    int x = 0;
    int y = 0;

    /*@
      loop invariant y == 0; // Invariant stating y is always zero
      loop invariant x == 0;  // Invariant stating x is always zero
      loop invariant z3 == \at(z3, Pre); // Invariant for z3's initial value
      loop invariant z2 == \at(z2, Pre); // Invariant for z2's initial value
      loop invariant z1 == \at(z1, Pre); // Invariant for z1's initial value
      loop assigns y; // Assignments that may occur in the loop
    */
    while(y >= 0) {
        y = y + x;
    }
    
    /*@ assert y >= 0;*/

}
