
typedef struct __CheckCal
{
        int pkv[10];
        int len;
        
} CheckCal;

/*@
    requires \valid(pIp);
    requires \valid(pIp->pkv + (0..9));
    requires \forall integer i; 0 <= i < 10 ==> 0 <= pIp->pkv[i] <= 100;
    requires  pIp->len <= 10;
    */
    
void CheckCalFun5(CheckCal *pIp){
        int i = 0;
        int chksum = 0;

        
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant 0 <= i <= pIp->len;
            loop invariant chksum == \sum(j in 0..i-1) pIp->pkv[j];
            */
            for (; i < pIp->len; i++){
            chksum = chksum + pIp->pkv[i];
        }
            

        return chksum;

}
