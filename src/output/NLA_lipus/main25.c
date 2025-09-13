
/*@
    requires x >= 0;
    */
    
int main25(int x,int w){
	
	int z = w * x;

	
            
        /*@ 
            loop invariant z == w * x * x^k; // where k is the number of iterations
            loop invariant w == \at(w, Pre) * x^k; // where k is the number of iterations
            loop invariant z == \at(w, Pre) * \at(x, Pre) * x^k; // where k is the number of iterations
            loop invariant x == \at(x, Pre);
            loop assigns w, z;
        */
            /*@
            */
            while(unknown())
	{
		w = w * x;
		z = z * x;
	}
            

	/*@ assert z == w * x; */
	return 0;
}
