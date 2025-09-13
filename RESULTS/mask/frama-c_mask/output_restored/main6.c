

void main6()
{
    int i=0;

    
            
            /*@
          loop invariant  0 <= i <= 30 ;
            */
            while (i<30){
        ++i;
    }
            
}

/* ===== Restored Assertions (from non-masked) ===== */
    /*@ assert i == 30; */
/* ===== End Restored Assertions ===== */
