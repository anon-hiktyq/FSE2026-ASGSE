
typedef struct TAG_DIGITAL_GYRO_DATA
{
    int countPick[9];		 		 	
    int wa[9];				 	
    int wal[9];				 
} SGyroData;

typedef struct __GyroPick
{
    SGyroData* pGyroData;
} GyroPick;

/*@ 
  assigns \nothing;
  ensures (x >= 0 ==> \result == x) && (x < 0 ==> \result == -x);
  ensures \result >= 0;
*/
int ABS(int x)
{
    if (x < 0)
        return -x;
    else
        return x;
}
