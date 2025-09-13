
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        

int hoo20(int idBitLength,int material_length,int nlen)

            /*@
            Require nlen == idBitLength / 32 && idBitLength >= 0 && material_length >= 0
            Ensure Results(__return)
            */
            {
    int j = 0;

    //pre-condition

    //loop-body
    while((j < idBitLength / 8) && (j < material_length)){
       j = j + 1;
    }

    //post-condition
    
}