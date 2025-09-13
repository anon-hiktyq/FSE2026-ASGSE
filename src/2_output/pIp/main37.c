
    #include "../verification_stdlib.h"
    #include "../verification_list.h"
    #include "../int_array_def.h"

    /*@ Extern Coq (Result: Assertion) */
    /*@ Extern Coq (Results: Z -> Assertion) */

        typedef struct Point {
    int x;
    int y;
} Point;
typedef struct _Point_Pair{
    Point p1;
    Point p2;
} Points;


int distance(Points* pIp) /*@
With pIp_p1_x pIp_p1_y pIp_p2_x pIp_p2_y
Require pIp->p1.x == pIp_p1_x && pIp->p1.y == pIp_p1_y && pIp->p2.x == pIp_p2_x && pIp->p2.y == pIp_p2_y
Ensure (__return == (pIp_p2_x - pIp_p1_x) * (pIp_p2_x - pIp_p1_x) + (pIp_p2_y - pIp_p1_y) * (pIp_p2_y - pIp_p1_y) && (pIp->p1.x == pIp_p1_x) * (pIp->p1.y == pIp_p1_y) * (pIp->p2.x == pIp_p2_x) * (pIp->p2.y == pIp_p2_y))
*/
{
    int dx = pIp->p2.x - pIp->p1.x;
    int dy = pIp->p2.y - pIp->p1.y;
    return dx * dx + dy * dy;
}
void main37(Points* pIp) 
/*@
With pIp_p1_x pIp_p1_y pIp_p2_x pIp_p2_y
Require pIp->p1.x == pIp_p1_x && pIp->p1.y == pIp_p1_y && pIp->p2.x == pIp_p2_x && pIp->p2.y == pIp_p2_y
Ensure (exists retval_94, retval_94 == (3 - 1) * (3 - 1) + (4 - 2) * (4 - 2) && (pIp->p1.x == 1) * (pIp->p1.y == 2) * (pIp->p2.x == 3) * (pIp->p2.y == 4))
*/
{
    pIp->p1.x = 1;
    pIp->p1.y = 2;
    pIp->p2.x = 3;
    pIp->p2.y = 4;
    int result = distance(pIp);
    
}