

typedef struct __Delay
{

	int			delaytime;

} Delay;

/*@
requires \valid(pIp) ;

ensures 0 >= \old(pIp->delaytime) ==> pIp->delaytime == \old(pIp->delaytime);

*/

void DelayFun(Delay* pIp)

{
    int t = 0;

    /*@
      loop invariant 0 <= t <= pIp->delaytime;
      loop invariant valid_delaytime(pIp);
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
    
void main33(Delay *pIp){

    pIp -> delaytime = 10;

    DelayFun(pIp);

    /*@ assert pIp -> delaytime == 10; */
}