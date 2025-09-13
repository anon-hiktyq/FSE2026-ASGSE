
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        


void foo039(int MAXPATHLEN,int  __BLAST_NONDET) 

            /*@
            Require MAXPATHLEN <= 0
            Ensure Results(__return)
            */
            {
  
  int buf_off;
  int pattern_off;
  int bound_off;

 
  int glob3_pathbuf_off;
  int glob3_pathend_off;
  int glob3_pathlim_off;
  int glob3_pattern_off;
  int glob3_dc;


  buf_off = 0;
  pattern_off = 0;

  
  bound_off = 0 + (MAXPATHLEN + 1) - 1;

  glob3_pathbuf_off = buf_off;
  glob3_pathend_off = buf_off;
  glob3_pathlim_off = bound_off;
  glob3_pattern_off = pattern_off;

  glob3_dc = 0;

 
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    (0 <= glob3_dc && glob3_dc <= 1 // Adjusted to account for MAXPATHLEN <= 0) &&
(glob3_pattern_off == 0) &&
(glob3_pathlim_off == 0 + (MAXPATHLEN@pre + 1) - 1) &&
(glob3_pathend_off == 0) &&
(glob3_pathbuf_off == 0) &&
(bound_off == 0 + (MAXPATHLEN@pre + 1) - 1) &&
(pattern_off == 0) &&
(buf_off == 0) &&
(__BLAST_NONDET == __BLAST_NONDET@pre) &&
(MAXPATHLEN == MAXPATHLEN@pre
              loop assigns glob3_dc)
    */
    
            for (;;){
    if (glob3_pathend_off + glob3_dc >= glob3_pathlim_off) break;
    else {
     
      glob3_dc++;
     
      /*@ assert 0 <= glob3_dc;*/
      /*@ assert glob3_dc < MAXPATHLEN + 1; */
      if (unknown()) return;
    }
}

}