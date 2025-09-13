#include<limits.h>

/*@
requires p >= 0 && n >= 0 && r >= 0;
requires p <= INT_MAX && n <= INT_MAX && r <= INT_MAX;
requires INT_MIN <= r <= INT_MAX;
requires INT_MIN <= p <= INT_MAX;
requires INT_MIN <= n <= INT_MAX;
requires (p * n * r) / 100 <= INT_MAX; // To prevent overflow;
requires (p * n * r) / 100 <= INT_MAX; // To avoid overflow;
ensures \result == p * n * r / 100;
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