
int main(){

  float a[10000], b[10000], t;
  int i, n;
  
  n = 10000;
  for (i=1; i<n; i++) {
    t = a[i]+b[i];
    b[i] =  t + t*t;
  }
	
   return 0;
}
