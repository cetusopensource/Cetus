
int main(){

  float a[10000], b[10000];
  int i, n, ind, ind2;
  
  n = 10000;
  ind = 123;
  for (i=1; i<n; i++) {
    ind = ind + 2;
    a[ind] = b[i];
  }

  ind2 = 5;
  ind = 234;
  for (i=1; i<n; i++) {
    ind = ind + 2;
    ind2 = ind2 + ind;
    a[ind2] = b[i];
  }
	
   return 0;
}
