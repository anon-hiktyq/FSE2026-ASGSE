
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        typedef struct __CheckCal
{
        int *pkv;
        int len;

} CheckCal;


int CheckCalFun(CheckCal *pIp)
/*@
With pIp_pkv_v pIp_pkv pIp_len
Require *(pIp->pkv) == pIp_pkv_v && (pIp->pkv) == pIp_pkv && pIp->len == pIp_len
Ensure Results(__return)
*/
{
        int i = 0;
        int chksum = 0;

       
  /*@ Print user assertion at number LoopEntry_0*/ 
/*@ Inv
    ((0 < pIp@pre->len) => (0 <= i && i <= pIp@pre->len)) &&
((0 < pIp@pre->len) => (chksum == sum(pIp->pkv, 0, i))) &&
((!(0 < pIp@pre->len)) => ((chksum == 0)&&(i == 0)&&(pIp == pIp@pre)&&(pIp@pre->pkv == pIp_pkv)&&(*pIp_pkv == pIp_pkv_v)&&(pIp@pre->len == pIp_len))) &&
(pIp == pIp@pre) &&
(pIp@pre->pkv == pIp_pkv) &&
(*pIp_pkv == pIp_pkv_v) &&
(pIp@pre->len == pIp_len) &&
(forall (k:Z), 0 <= k && k < i => pIp->pkv_l[k] == pIp->pkv_l[k]@pre
          loop assigns i, chksum)
    */
    
        for (; i < pIp->len; i++)
        {
            chksum = chksum + pIp->pkv[i];
        }


        return chksum;

}
void main(CheckCal *pIp)

/*@
With pIp_pkv_v pIp_pkv pIp_len
Require *(pIp->pkv) == pIp_pkv_v && (pIp->pkv) == pIp_pkv && pIp->len == pIp_len
Ensure emp
*/{

    pIp->len = 3;
    int chksum = CheckCalFun(pIp);
    

}