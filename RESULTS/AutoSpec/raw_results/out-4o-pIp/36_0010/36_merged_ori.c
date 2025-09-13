 typedef struct Point {
    int x;
    int y;
} Point;

typedef struct _Point_Pair{
    Point p1;
    Point p2;
} Points;


/*@
requires \valid(pIp);
requires \valid(&pIp- > p2);
requires \valid(&pIp- > p1);
requires \valid(&(pIp- > p1)) && \valid(&(pIp- > p2));
ensures \result >= 0;
ensures \result == (pIp- > p2.x - pIp- > p1.x) * (pIp- > p2.x - pIp- > p1.x) + (pIp- > p2.y - pIp- > p1.y) * (pIp- > p2.y - pIp- > p1.y);
assigns \nothing;
*/
int distance(Points* pIp) {
    int dx = pIp->p2.x - pIp->p1.x;
    int dy = pIp->p2.y - pIp->p1.y;
    return dx * dx + dy * dy;
}


void main36(Points* pIp) {
    pIp->p1.x = 1;
    pIp->p1.y = 2;
    pIp->p2.x = 3;
    pIp->p2.y = 4;
    int result = distance(pIp);
    // @ assert result == 8;
    // @ assert pIp->p1.x == 1;
    // @ assert pIp->p1.y == 2;
    // @ assert pIp->p2.x == 3;
    // @ assert pIp->p2.y == 4;
}

