#include<limits.h>

/*@
requires p >= 0 && n >= 0 && r >= 0;
requires p * n * r <= INT_MAX * 100; // To avoid overflow
ensures \result == (p * n * r) / 100;
assigns \nothing;
*/
int simple(int p,int n,int r)
{
    int si;
    si = p*n*r/100;
    return si;
}
 
int main()
{
    int s = simple(10000, 3,10);
    return 0;
}