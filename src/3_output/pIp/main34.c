

typedef struct __Delay
{

	int			delaytime;

} Delay;

/*@
requires \valid(pIp);
requires 0 <= pIp->delaytime <= 10;

ensures 0 >= \old(pIp->delaytime) ==> pIp->delaytime == \old(pIp->delaytime);

*/

void DelayFun(Delay* pIp)

{
    int t = 0;

    /*@ loop invariant 0 <= t <= pIp->delaytime;
        loop assigns t;
    */
    for (; t < pIp->delaytime; t++)
    {
        ;
    }

    /*@ assert t >= 0; */

    return;
}/*@
    requires \valid(pIp);
    */
    
void main34(Delay *pIp){
    pIp -> delaytime = 10;

    DelayFun(pIp);

    /*@ assert pIp -> delaytime == 10; */
}