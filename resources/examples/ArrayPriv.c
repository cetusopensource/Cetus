
int main(){

  float a[1000][1000], b[1000][1000], t[1000];
  int i, j;
  
  for (i=1; i<1000; i++) {
     for (j=1; j<1000; j++) {
       t[j] = a[i][j]+b[i][j];
     }
     for (j=1; j<1000; j++) {
       b[i][j] =  t[j] + sqrt(t[j]);
     }
  }
	
   return 0;
}
