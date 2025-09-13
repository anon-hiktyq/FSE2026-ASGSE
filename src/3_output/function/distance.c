typedef struct Point {
    int x;
    int y;
} Point;
typedef struct _Point_Pair{
    Point p1;
    Point p2;
} Points;
/*@
    
    */
    
int distance(Points* pIp) {
    int dx = pIp->p2.x - pIp->p1.x;
    int dy = pIp->p2.y - pIp->p1.y;
    return dx * dx + dy * dy;
}