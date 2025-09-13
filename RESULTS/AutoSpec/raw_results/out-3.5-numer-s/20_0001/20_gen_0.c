//svcomp_id_trans
/*@
  requires nlen == idBitLength / 32;
  requires idBitLength >= 0;
  requires material_length >= 0;
*/
void hoo20(int idBitLength,int material_length,int nlen){
    int j = 0;

    //pre-condition

    //loop-body
    /*@
    Looking at this function, I need to analyze the loop behavior and the post-condition that needs to be satisfied.
    
    The loop increments `j` from 0 while `j < idBitLength / 8` and `j < material_length`. The post-condition asserts `(j / 4) <= nlen`, and we know from the precondition that `nlen == idBitLength / 32`.
    
    ```c
    loop invariant 0 <= j;
    loop invariant j <= idBitLength / 8;
    loop invariant j <= material_length;
    loop invariant (j / 4) <= nlen;
    loop assigns j;
    ```
    */
    while((j < idBitLength / 8) && (j < material_length)){
       j = j + 1;
    }

    //post-condition
    /*@ assert (j / 4) <= nlen; */
}