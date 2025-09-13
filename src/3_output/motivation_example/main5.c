typedef struct __CheckCal
{
        int pkv[10];
        int len;
        
} CheckCal;


typedef struct __CheckCal
{
    int pkv[10];
    int len;
        
} CheckCal;

/*@
    requires \valid(pIp);
    requires \valid(pIp->pkv + (0..9));
    requires \forall integer i; 0 <= i < 10 ==> 0 <= pIp->pkv[i] <= 100;
    requires pIp->len <= 10;
    assigns \nothing;
    ensures \result == \sum_from_to(0, pIp->len-1, \lambda integer j; pIp->pkv[j]);
*/
    
int CheckCalFun5(CheckCal *pIp){
    int i = 0;
    int chksum = 0;

    /*@
        loop invariant 0 <= i <= pIp->len;
        loop invariant chksum == \sum_from_to(0, i-1, \lambda integer j; pIp->pkv[j]);
        loop assigns i, chksum;
        loop variant pIp->len - i;
    */
    for (; i < pIp->len; i++){
        chksum = chksum + pIp->pkv[i];
    }
    
    return chksum;
}
/*@
    requires \valid(pIp);
    requires \valid(pIp->pkv + (0..9));
    requires \forall integer i; 0 <= i < 10 ==> 0 <= pIp->pkv[i] <= 100;
    requires pIp->len <= 10;
    */
    
void main5(CheckCal *pIp)
{
    
    pIp->len = 3;
    int chksum = CheckCalFun5(pIp);
    

}