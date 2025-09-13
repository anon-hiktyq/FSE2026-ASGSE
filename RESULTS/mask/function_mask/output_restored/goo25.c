
typedef struct __CheckCal
{
	int len;
	int *pkv;
	int chksum;
} CheckCal;

/*@
axiomatic Sum_array {
  logic integer sum(int* array, integer begin, integer end) reads array[begin .. (end-1)];
  axiom empty:
    \forall int* a, integer b, e; b >= e ==> sum(a,b,e) == 0;
  axiom range:
    \forall int* a, integer b, e; b < e ==> sum(a,b,e) == sum(a,b,e-1) + a[e-1];
}
*/

/*@
requires \valid(pIp);
requires \valid(pIp->pkv+(0..9));
requires pIp->len <= 10;
requires \forall integer i; 0 <= i < 10 ==> 0 <= pIp->pkv[i] && pIp->pkv[i] <= 100;
*/
void goo25(CheckCal *pIp)
{
	int i = 0;
	int chksum = 0;

	/*@
	  loop invariant (0 < \at(pIp,Pre)->len) ==> (0 <= i <= \at(pIp,Pre)->len);
	  loop invariant (0 < \at(pIp,Pre)->len) ==> (chksum == sum(\at(pIp,Pre)->pkv, 0, i));
	  loop invariant (!(0 < \at(pIp,Pre)->len)) ==> ((chksum == 0) && (i == 0) && (pIp == \at(pIp,Pre)) && (\at(pIp,Pre)->len == pIp->len) && (\at(pIp,Pre)->pkv == \at(pIp->pkv,Pre)) && (*\at(pIp->pkv,Pre) == \at(*pIp->pkv,Pre)) && (\at(pIp,Pre)->chksum == \at(pIp->chksum,Pre)));
	  loop invariant pIp == \at(pIp,Pre);
	  loop invariant \at(pIp,Pre)->len == pIp->len;
	  loop invariant \at(pIp,Pre)->pkv == \at(pIp->pkv,Pre);
	  loop invariant *\at(pIp->pkv,Pre) == \at(*pIp->pkv,Pre);
	  loop invariant \at(pIp,Pre)->chksum == \at(pIp->chksum,Pre);
	  loop invariant \forall integer j; 0 <= j < i ==> 0 <= pIp->pkv[j] && pIp->pkv[j] <= 100;
	  loop assigns i, chksum;
	  loop variant pIp->len - i;
	*/
	for (; i < pIp->len; i++)
	{
		chksum = chksum + pIp->pkv[i];
	}


	/*@ assert pIp->len == \at(pIp->len,Pre); */
	/*@ assert pIp->chksum == \at(pIp->chksum,Pre); */
    /*@ assert chksum >= 0; */

	pIp->chksum = chksum;

	return;
}
