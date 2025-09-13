
typedef struct __CheckCal
{

	int		len;
	int		*pkv;
	int     chksum;
	
} CheckCal;

/*@
    predicate valid_sum{L}(int* array, integer begin, integer end, integer sum) =
        sum == \sum(array + begin, array + end);

    requires \valid(pIp);
    requires \valid(pIp->pkv + (0 .. pIp->len - 1));
    requires pIp->len <= 10;
    requires \forall integer i; 0 <= i < pIp->len ==> 0 <= pIp->pkv[i] && pIp->pkv[i] <= 100;
*/
void main25(CheckCal *pIp)
{

	int i = 0;
	int chksum = 0;

	
            
    /*@
        loop invariant 0 <= i <= pIp->len;
        loop invariant valid_sum(pIp->pkv, 0, i, chksum);
        loop assigns i, chksum;
    */
    for(; i < pIp->len; i++)
	{
	    chksum = chksum + pIp->pkv[i];
	}
            

	
	/*@ assert pIp->len == \at(pIp->len,Pre); */
	/*@ assert pIp->chksum == \at(pIp->chksum,Pre); */
    /*@ assert chksum >= 0; */

	pIp->chksum = chksum;


	return;
}
