
/*@
    requires nlen == idBitLength / 32;
    requires idBitLength >= 0;
    requires material_length >= 0;
*/

int hoo20(int idBitLength,int material_length,int nlen){
    int j = 0;

    //pre-condition

    //loop-body
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant ((0 < \at(idBitLength,Pre) / 8) && (0 < \at(material_length,Pre))) ==> (0 <= j <= (\at(idBitLength,Pre) / 8 < \at(material_length,Pre) ? \at(idBitLength,Pre) / 8 : \at(material_length,Pre)));
            loop invariant (!((0 < \at(idBitLength,Pre) / 8) && (0 < \at(material_length,Pre)))) ==> ((j == 0)&&(nlen == \at(nlen,Pre))&&(material_length == \at(material_length,Pre))&&(idBitLength == \at(idBitLength,Pre)));
            loop invariant nlen == \at(nlen,Pre);
            loop invariant material_length == \at(material_length,Pre);
            loop invariant idBitLength == \at(idBitLength,Pre);
            loop assigns j;
            */
            while((j < idBitLength / 8) && (j < material_length)){
       j = j + 1;
    }
            

    //post-condition
    /*@ assert (j / 4) <= nlen; */
}
