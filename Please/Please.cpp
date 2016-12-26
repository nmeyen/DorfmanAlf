// Please.cpp : Defines the entry point for the console application.
//
#define _CRT_SECURE_NO_WARNINGS
#include "ranlib.h"
#define ANSI
#include "stdafx.h"
#include <math.h>
#define TINY 1.0e-20
#include <iostream>
#include <stdlib.h>
#include <stdio.h>
#include "nr.h"
#include "nrutil.h"
#ifndef PI
#define PI 3.141592653589793238462643
#endif

//***************************************************************************//
//    DORFMANN AND ALF MAXIMUM LIKELIHOOD ESTIMATION PROGRAM FOR  // //                                                    RATING LEVEL DATA                                                        //
//                                                                                                                                                     //                                                                                     //                                                                                                                                                     // 
//                                                                                                                                                     //
//                                                                                                                                                     //
//***************************************************************************//

/* multiply a matrix a by vector b, result in y. y can be same as b */
void fmvmult( float **a, int a_rows, int a_cols, float *b,float*y)
{
   int i, k;
   float sum;

   for ( i=1; i<=a_rows; i++ ) {
      sum = 0.0;
      for ( k=1; k<=a_cols; k++ ) sum += a[i][k]*b[k];
      y[i] = sum;
   }
}

/*Add two vectors a and b  together  and store result in y*/
void fvadd( float *a, int a_els, float *b, float *y)
{
   int j;

   for ( j=1; j<=a_els; j++ ) {
      y[j] = a[j] + b[j];
   }
}

/* multiply a by scalar r, result in y. y can be same as a */
void dmsmy( double **a, int a_rows, int a_cols, double r, double **y)
{
   int i, j;
   for ( i=1; i<=a_rows; i++ ) 
      for ( j=1; j<=a_cols; j++ ) {
         y[i][j] = a[i][j] * r;
      }
}


float slope,y_intercept; /*Declared as global variables*/
void lsquares(float *x, float *y, int n) /*Simple linear regression*/
{
 float SUMx, SUMy, SUMxy, SUMxx;
 int i;
 SUMx = 0; SUMy = 0; SUMxy = 0; SUMxx = 0;
   for (i=1; i<=n ;i++) {
    SUMx = SUMx + x[i];
    SUMy = SUMy + y[i];
    SUMxy = SUMxy + x[i]*y[i];
    SUMxx = SUMxx + x[i]*x[i];
  }
   if (SUMx*SUMx == n*SUMxx) {
	   printf("Slope cannot be fitted\n");
    }
   else {
        slope = ( SUMx*SUMy - n*SUMxy ) / ( SUMx*SUMx - n*SUMxx );
        y_intercept = ( SUMy - slope*SUMx ) / n;
   }
 }

void ludcmp(float **a, int n, int *indx, float *d) /*LU Decompostion of matrix prior to inversion*/
{
	int i, imax, j, k;
	float big, dum, sum, temp;
	float *vv;
	vv= nrvector(1,n);
	*d=1.0;

	for (i=1;i<=n;i++){
		big=0.0;
	for(j=1;j<=n;j++){
		if(fabs(a[i][j])>big) big=fabs(a[i][j]);
		}



	if(big==0) {
		nrerror("Singular matrix in routine ludcmp");
	 }

	vv[i]=1.0/big;
	  }
	for (j=1;j<=n;j++){
		for (i=1;i<j;i++){
			sum=a[i][j];
			for (k=1;k<i;k++) sum -= a[i][k]*a[k][j];
			a[i][j]=sum;
		}
		big=0.0;
		for(i=j;i<=n;i++) {
			sum=a[i][j];
		for (k=1;k<j;k++)
			sum -= a[i][k]*a[k][j];
		a[i][j]=sum;
		if((dum=vv[i]*fabs(sum))>=big){
			big=dum;
	        imax=i;
		}
	  }
	if (j != imax){
		for (k=1;k<=n;k++){
			dum=a[imax][k];
			a[imax][k]=a[j][k];
			a[j][k]=dum;
		}
		*d=-(*d);
		vv[imax]=vv[j];
	 }
	indx[j]=imax;
	if(a[j][j]==0.0) a[j][j]=TINY;
	 if (j !=n){
		dum=1.0/(a[j][j]);
		for(i=j+1;i<=n;i++) a[i][j] *=dum;
	  }
	}


	free_nrvector(vv,1,n);

}

void lubksb(float **a, int n, int *indx, float b[])/* LU backsubstitution to find the inverse of a matrix*/

{
	int i, ii=0, ip, j;
	float sum;

	for(i=1; i<=n; i++){
		ip=indx[i];
		sum=b[ip];
		b[ip]=b[i];
		if (ii)
		for(j=ii;j<=i-1;j++) sum -= a[i][j]*b[j];
		else if (sum) ii=i;
		b[i]=sum;
	  }
	for (i=n;i>=1;i--){
		sum=b[i];
		for (j=i+1;j<=n;j++) sum -= a[i][j]*b[j];
		b[i]=sum/a[i][i];
      }
 }


float normsin( float p)/*Inverse of the standard normal probability distribution http://home.online.no/~pjacklam/notes/invnorm/  */
{
/*Coefficients in rational approximations*/

float a[6] = {-3.969683028665376e+01,2.209460984245205e+02,-2.759285104469687e+02,1.383577518672690e+02,-3.066479806614716e+01,2.506628277459239e+00};

float b[5] = {-5.447609879822406e+01,  1.615858368580409e+02,-1.556989798598866e+02,  6.680131188771972e+01, -1.328068155288572e+01};

float c[6] = {-7.784894002430293e-03, -3.223964580411365e-01,-2.400758277161838e+00, -2.549732539343734e+00,4.374664141464968e+00,  2.938163982698783e+00};

float d[4] = {7.784695709041462e-03, 3.224671290700398e-01,2.445134137142996e+00,  3.754408661907416e+00};

/*Define break points*/

float plow = 0.02425;
float phigh = 1 - plow;

/*Rational approximation for lower region*/
if ( p < plow ) {
   float q = sqrt(-2*log(p));
return (((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) /
                                             ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1);
}
/* Rational approximation for upper region*/
else if ( phigh < p ) {
   float q = sqrt(-2*log(1-p));
return -(((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) /
                                                    ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1);
}

/* Rational approximation for central region*/

else{
   float q = p - 0.5;
   float r = q*q;
   return (((((a[0]*r+a[1])*r+a[2])*r+a[3])*r+a[4])*r+a[5])*q /
                             (((((b[0]*r+b[1])*r+b[2])*r+b[3])*r+b[4])*r+1);
 }
}


float norms(float z)/*standad normal probability density function http://finance.bi.no/~bernt/gcc_prog/recipes/recipes/node23.html */
 {
  return (1.0/sqrt(2.0*PI))*exp(-0.5*z*z);
 }


float normscum(float z)/*Standard normal cumulative density function http://finance.bi.no/~bernt/gcc_prog/recipes/recipes/node23.html */
 {
	 if (z > 6.0) {return 1.0;}; // This guards against overflow
	 if (z < -6.0) {return 0.0;};
	 float b1 = 0.31938153;
     float b2 = -0.356563782;
	 float b3 = 1.781477937;
	 float b4 = -1.821255978;
	 float b5 = 1.330274429;
	 float p = 0.2316419;
             float c2 = 0.3989423;

	 float a = fabs(z);
	 float t = 1.0/(1.0+a*p);
	 float b = c2*exp((-z)*(z/2.0));
	 float n = ((((b5*t+b4)*t+b3)*t+b2)*t+b1)*t;
	 n = 1.0 - b*n;
	 if (z <0.0) n = 1.0-n;
	 return n;
}


void readinTP(float *a,int n)/*Read in true positive data*/
{
  for (int i = 1; i <= n; i++)
    {
      printf("\nTrue positive number for category no: %d: ", i );
      scanf("%f", &a[i]);
	  if (a[i] == 0.0) {    /*If a[i] == 0 add a small positive constant 1*/
		  a[i] = 1;
	 }
    }
  return;
}



int matrixinv(float **A,int n,float **B){
float d,*col;/*parameters required for matrix inversion*/
int *indx;/*parameter required for matrix inversion*/

indx = ivector(1,n);
col = nrvector(1,n);

/*Inversion of the second partial derivative matrix using LU decomposition*/
if (ludcmp == 0 ){
   return 0;
}

else {
ludcmp(A,n,indx,&d);
  for(int j=1;j<=n ;j++) {
    for(int i=1;i<=n;i++)
		col[i]=0.0;
        col[j]=1.0;
lubksb(A,n,indx,col);
     for(int i=1;i<=n;i++)
		 B[i][j]=col[i];
  }

   free_ivector(indx,1,n);
   free_nrvector(col,1,n);
 }
}


int _tmain(int argc, _TCHAR* argv[]){
  FILE *fp1;

  fp1 = fopen("F:\\1mean_1.5sd_size120_p.txt","w");

  int n1;/*Number of groups under consideration*/
  n1 = 3;


//****************************************************************************//                              //                                   Functions related to random number generation                                        //
//****************************************************************************//

static long gen = 1;

  
setall(500L,1000L); //   Set up Generators
gscgn(1,&gen); //Set to Generator 1

int counter2;
    for (counter2=1;counter2 <=1000;counter2 ++){
	
   
float *vec1;
vec1 = new float[60];

for (int i=0;i<60;i++)
{ 
 vec1[i]=0;
}

float *vec2;
vec2 = new float[60];
for (int i=0;i<60;i++)
{ 
 vec2[i]=0;
}

//Generate normal deviates with mean 0.5 and standard deviation 0.1
for (int i=0;i<60;i++)
{ 
 vec1[i]=gennor(0.5,0.1);
 advnst(2L);
}

//Generate normal deviates with mean 0.6 and standard deviation 0.15
for (int i=0;i<60;i++)
{ 
 vec2[i]=gennor(0.6,0.15);
 advnst(2L);
}

int *cat1;
cat1 = new int [3];

//Initialize the vector cat1 so that all its elements are zero


for (int i=0; i<3;i++)
{ 
  cat1[i] =0;
}

//Store the normal deviates according to cut points
for (int i=0;i<60;i++)
{
 if (vec1[i]< 0.4587537){
   cat1[0] = cat1[0]+1;
    }
 else if (vec1[i] >= 0.4587537 && vec1[i] < 0.5439913){
   cat1[1] = cat1[1]+1;
   }
 else if (vec1[i]>= 0.5439913){
   cat1[2]= cat1[2]+1;
   }
 }

int *cat2;
cat2 = new int [3];

//Initialize the vector cat2 so that all its elements are zero
for (int i=0; i<3;i++)
{ 
  cat2[i] =0;
}

//Store the normal deviates according to cut points 
for (int i=0;i<60;i++)
{
 if (vec2[i]< 0.4587537){
   cat2[0] = cat2[0]+1;
    }
 else if (vec2[i] >= 0.4587537 && vec2[i] < 0.5439913){
   cat2[1] = cat2[1]+1;
   }
 else if (vec2[i]>= 0.5439913){
   cat2[2] = cat2[2] +1;
   }
 }

 float *r1;
	r1 = nrvector(1,n1);

	 for(int i = 1; i<=n1;i++){
		 if (cat1[i-1] == 0) {    /*If a[i] == 0 add a small positive constant 1*/
			 cat1[i-1] = 1;
		 }
       r1[i] = float (cat1[i-1]);
	 }

  float *r2;
	 r2 = nrvector(1,n1);

	 for(int i = 1; i<=n1;i++){
		 if (cat2[i-1] == 0) {    /*If a[i] == 0 add a small positive constant 1*/
			 cat2[i-1] = 1;
		 }
       r2[i] = float (cat2[i-1]);
	 }


	for (int i = 0; i < 3; i++)
    {
       fprintf(fp1,"%d,", cat1[i]); /*Print numbers in categories*/
    }

   for (int i = 0; i < 3; i++)
    {
       fprintf(fp1,"%d,", cat2[i]); /*Print numbers in categories*/
    }


 int n2;/*Number of Z'k s*/  
 n2 = n1-1;


 float r1i;/*Total number of false positives*/
 float r2i;/*Total number of true positives*/


 r1i = 0 ;
 for (int i = 1; i<= n1 ; i++){
   r1i = r1i + r1[i];
  }


 r2i = 0 ;
 for (int i = 1; i<= n1 ; i++){
   r2i = r2i + r2[i];
  }

 float **p; /* referred to as pi in the literature review*/
 p = matrix (1,n1,1,2);

 for (int i = 1; i<=n1 ;i++){
  p[1][i] = r1[i]/r1i;
 }

  for (int i = 1; i<=n1 ;i++){
  p[2][i] = r2[i]/r2i;
 }

 float *phi1;/*Vector 1 for initial regression*/
 phi1= nrvector(1,n2);
 for (int i =1;i<=n2;i++){
	 phi1[i]=0;
 }

  for (int i =1 ;i<=n2;i++){
   for(int counter1=1;counter1 <= i;counter1++){
   phi1[i] = p[1][counter1] + phi1[i];
   }
 }


 float *phi2;/*Vector 2 for initial regression*/
 phi2= nrvector(1,n2);
 for (int i =1;i<=n2;i++){
	 phi2[i]=0;
 }

  for (int i =1 ;i<=n2;i++){
   for(int counter1=1;counter1 <= i;counter1++){
   phi2[i] = p[2][counter1] + phi2[i];
   }
 }


float *izk1;/*initial vector of zk1's */
izk1 = nrvector(1,n2);
  for(int i =1 ;i<=n2; i++){
   izk1[i] = normsin(phi1[i]);
  }


float *izk2;/*initial vector of zk2's */
izk2 = nrvector(1,n2);
  for(int i =1 ;i<=n2; i++){
   izk2[i] = normsin(phi2[i]);
  }

float b1;/*Initial estimate of b*/
float a1;/*Initial estimate of a*/


lsquares(izk1,izk2,n2); /*Simple linear regression for initial parameter estimates*/
b1 = slope;
a1 = -y_intercept;


float *theta2;/*Vector of previous parameter estimates*/
theta2 = nrvector(1,n2+2);

float *theta3;/*Vector of intermediate parameter estimates*/
theta3 = nrvector(1,n2+2);

float *theta4;/*Vector of next parameter estimates*/
theta4 = nrvector(1,n2+2);

float *thetadif;/*Vector of difference of parameter estimates*/
thetadif = nrvector(1,n2+2);

float *zk1;/*vector of zk1's*/
zk1 = nrvector(1,n2);
for(int i =1;i<=n2;i++){
	zk1[i]= izk1[i];
}


float a;/*Parameter estimate for a */
float b;/*Parameter estimate for b */

a = a1;
b = b1;

float *theta1;/*Vector of initial parameter estimates*/
theta1 = nrvector(1,n2+2);
theta1[1] = a1;
theta1[2] = b1;


 for(int i=3;i<=n2+2;i++){
	theta1[i]= izk1[i-2];
 }


 for (int i=1;i<=n2+2;i++){
	 theta2[i]=theta1[i];
 }


 float *F1;/*Vector of cumulative std. normal 1*/
 F1 = nrvector(0,n1);
 for (int i =1;i<=n2;i++){
   F1[i] = normscum(izk1[i]);
 }
 F1[0] = 0;
 F1[n1] = 1;


 float *F2;/*Vector of cumulative std. normal 2*/
 F2 = nrvector(0,n1);
 for (int i =1;i<=n2;i++){
   F2[i] = normscum(b1*izk1[i]-a1);
 }
 F2[0] = 0;
 F2[n1] = 1;


 float *f1;/*Vector of std. normal 1*/
  f1 = nrvector(0,n1);
 for (int i =1;i<=n2;i++){
  f1[i]= norms(izk1[i]);
 }
  f1[0]=0;
  f1[n1]=0;


 float *f2;/*Vector of std. normal 2*/
  f2 = nrvector(0,n1);
 for (int i =1;i<=n2;i++){
  f2[i]= norms(b1*izk1[i]-a1);
 }
  f2[0]=0;
  f2[n1]=0;



  int counterp;/*counter for while loop*/
  counterp = 0;

  int check1;/* A variable to check if while loop is true*/
  int check2;/*A variable to check if while loop is true*/



  while ( (counterp < 200)){ /*Iterative loop until convergence is reached*/

  check1 = 0;
  check2 = 0;

  float *lambda;/*first derivative estimates*/
  lambda = nrvector(1,n2+2);

  float spartial1;/*first partial derivative sum*/
  spartial1 = 0;

 for (int i =1;i<=n2;i++){
   spartial1 = spartial1 + (f2[i]*((p[2][i]/(F2[i]-F2[i-1]))-(p[2][i+1]/(F2[i+1]-F2[i]))));
  }

  lambda[1] = -r2i*spartial1;/*first partial derivative element*/

 float spartial2;/*second partial derivative sum*/
 spartial2 = 0;

 for (int i =1;i<=n2;i++){
   spartial2 = spartial2 + (f2[i]*zk1[i]*((p[2][i]/(F2[i]-F2[i-1]))-(p[2][i+1]/(F2[i+1]-F2[i]))));
  }
 lambda[2] = r2i*spartial2;/*second partial derivative element*/

float spartial3a;/*other partial sum*/
float spartial3b;
spartial3a = 0;
spartial3b = 0;

for (int i=1;i<=n2; i++){
	spartial3a = f2[i]*b*(((r2[i])/(F2[i]-F2[i-1]))-((r2[i+1])/(F2[i+1]-F2[i])));
	spartial3b = f1[i]*(((r1[i])/(F1[i]-F1[i-1]))-((r1[i+1])/(F1[i+1]-F1[i])));
	lambda[i+2] = spartial3a + spartial3b;
}


float **A;/*Matrix of second derivatives*/
 A = matrix(1,n2+2,1,n2+2);
  for(int i =1 ;i<=n2+2; i++){
    for(int j =1 ;j<=n2+2; j++){
     A[i][j]= 0;
   }
 }


 /*Get expected second and mixed partials*/

 float spartiala11;
 spartiala11 = 0;

 for (int i=1;i<=n2; i++) {
 spartiala11 = spartiala11 + f2[i]*(((f2[i]-f2[i-1])/(F2[i]-F2[i-1]))-((f2[i+1]-f2[i])/(F2[i+1]-F2[i])));
 }

 A[1][1] = r2i*spartiala11; /*Second partial derivative of a*/

 float spartiala22;
 spartiala22 = 0;

 for (int i=1;i<=n2; i++) {
 spartiala22 = spartiala22 + f2[i]*zk1[i]*(((f2[i]*zk1[i]-f2[i-1]*zk1[i-1])/(F2[i]-F2[i-1]))-((f2[i+1]*zk1[i+1]-f2[i]*zk1[i])/(F2[i+1]-F2[i])));
 }

 A[2][2] = r2i*spartiala22; /*Second partial derivative of b*/

float spartiala12;
spartiala12 = 0;

for(int i=1;i<=n2;i++){
spartiala12 = spartiala12 + f2[i]*zk1[i]*(((f2[i]- f2[i-1])/(F2[i]-F2[i-1]))-((f2[i+1]-f2[i])/(F2[i+1]-F2[i])));
}

A[1][2] = -r2i*spartiala12;/*second partial derivative of a to b*/

A[2][1] = A[1][2];

/*Second partial derivative of cell ai+2 to ai+2*/
for(int i=1;i<=n2;i++){
A[i+2][i+2] = r2i*f2[i]*(pow(b,2))*(((f2[i])/(F2[i]-F2[i-1]))+((f2[i])/(F2[i+1]-F2[i]))) + r1i*f1[i]*(((f1[i])/(F1[i]-F1[i-1]))+((f1[i])/(F1[i+1]-F1[i])));
}

/*Second partial derivative of cell a1 to ai+2*/
for(int i=1;i<=n2;i++){
A[1][i+2] = -r2i*f2[i]*b*(((f2[i]-f2[i-1])/(F2[i]-F2[i-1]))-((f2[i+1]-f2[i])/(F2[i+1]-F2[i])));
A[i+2][1]= A[1][i+2];
}

/*Second partial derivative of cell a2 to ai+2*/
for(int i=1;i<=n2;i++){
A[2][i+2] = r2i*f2[i]*b*(((zk1[i]*f2[i]-zk1[i-1]*f2[i-1])/(F2[i]-F2[i-1]))-((zk1[i+1]*f2[i+1]-zk1[i]*f2[i])/(F2[i+1]-F2[i])));
A[i+2][2] = A[2][i+2];
}

/*Second partial derivative of cell ai+1 to ai+2*/
for(int i=2;i<=n2;i++){
A[i+1][i+2] = -((r2i*(pow(b,2))*f2[i]*f2[i-1])/(F2[i]-F2[i-1]))-((r1i*f1[i]*f1[i-1])/(F1[i]-F1[i-1]));
A[i+2][i+1] = A[i+1][i+2];
}

float **Ainv;/*Inverse matrix of A*/
Ainv = matrix(1,n2+2,1,n2+2);

matrixinv(A,n2+2,Ainv);/*Inversion of the matrix A*/


float *lambda1;/*Intermediate vector lambda*/
lambda1 = nrvector(1,n2+2);

if (matrixinv == 0 ){
// theta2
}

fmvmult(Ainv,n2+2,n2+2, lambda,lambda1);/*multiply and obtain the intermediate vector 
                                         prior to addition*/                      
  fvadd( theta2, n2+2, lambda1, theta4);


for (int i=1;i<=n2+2;i++){
	 theta3[i]=theta2[i];
 }


   for(int i=1;i<=n2;i++){
    zk1[i]=theta4[i+2];
 }

   for (int i=1;i<=n2+2;i++){
	 theta2[i]=theta4[i];
 }

   for (int i=1;i<=n2+2;i++){
	 thetadif[i]=fabs(theta4[i]-theta3[i]);
 }


   a = theta4[1];
   b = theta4[2];

   for (int i =1;i<=n2;i++){
   F1[i] = normscum(zk1[i]);
  }


  for (int i =1;i<=n2;i++){
   F2[i] = normscum(b*zk1[i]-a);
  }


  for (int i =1;i<=n2;i++){
  f1[i]= norms(zk1[i]);
 }


  for (int i =1;i<=n2;i++){
  f2[i]= norms(b*zk1[i]-a);
 }



for (int i=1;i<=n2+2;i++){
	 if (thetadif[i] < 0.001){
       check1 =  check1 + 1;
	 }
}

   for(int i=2;i<=n2;i++){
   if(zk1[i-1] <= zk1[i])
	  check2 = check2 + 1 ;
  }


   if (b>0 && check2 == n2-1 && check1 == n2+2){
 	   break;
   }


   free_nrvector(lambda,1,n2);
   free_nrvector(lambda1,1,n2);
   free_matrix(A,1,n2+2,1,n2+2);
   free_matrix(Ainv,1,n2+2,1,n2+2);

   counterp = counterp + 1;

 }/*end of while loop*/

 float AUC;/*Value for area under the curve*/
 float dabbaA;/*Partial derivative of the AUC with respect to a*/
 float dabbaB;/*Partial derivative of the AUC with respect to b*/
 float VAUC;/*Variance of AUC*/


/*Initializing all the elements of the matrix to 0*/
float **A;/*Matrix of second derivatives*/
 A = matrix(1,n2+2,1,n2+2);

  for(int i =1 ;i<=n2+2; i++){
    for(int j =1 ;j<=n2+2; j++){
     A[i][j]= 0;
   }
 }


 /*Get expected second and mixed partials*/

 float spartiala11;
 spartiala11 = 0;

 for (int i=1;i<=n2; i++) {
 spartiala11 = spartiala11 + f2[i]*(((f2[i]-f2[i-1])/(F2[i]-F2[i-1]))-((f2[i+1]-f2[i])/(F2[i+1]-F2[i])));
 }

 A[1][1] = r2i*spartiala11; /*Second partial derivative of a*/

 float spartiala22;
 spartiala22 = 0;

 for (int i=1;i<=n2; i++) {
 spartiala22 = spartiala22 + f2[i]*zk1[i]*(((f2[i]*zk1[i]-f2[i-1]*zk1[i-1])/(F2[i]-F2[i-1]))-((f2[i+1]*zk1[i+1]-f2[i]*zk1[i])/(F2[i+1]-F2[i])));
 }

 A[2][2] = r2i*spartiala22; /*Second partial derivative of b*/

float spartiala12;
spartiala12 = 0;

for(int i=1;i<=n2;i++){
spartiala12 = spartiala12 + f2[i]*zk1[i]*(((f2[i]- f2[i-1])/(F2[i]-F2[i-1]))-((f2[i+1]-f2[i])/(F2[i+1]-F2[i])));
}

A[1][2] = -r2i*spartiala12;/*second partial derivative of a to b*/

A[2][1] = A[1][2];

/*Second partial derivative of cell ai+2 to ai+2*/
for(int i=1;i<=n2;i++){
A[i+2][i+2] = r2i*f2[i]*(pow(b,2))*(((f2[i])/(F2[i]-F2[i-1]))+((f2[i])/(F2[i+1]-F2[i]))) + r1i*f1[i]*(((f1[i])/(F1[i]-F1[i-1]))+((f1[i])/(F1[i+1]-F1[i])));
}

/*Second partial derivative of cell a1 to ai+2*/
for(int i=1;i<=n2;i++){
A[1][i+2] = -r2i*f2[i]*b*(((f2[i]-f2[i-1])/(F2[i]-F2[i-1]))-((f2[i+1]-f2[i])/(F2[i+1]-F2[i])));
A[i+2][1]= A[1][i+2];
}

/*Second partial derivative of cell a2 to ai+2*/
for(int i=1;i<=n2;i++){
A[2][i+2] = r2i*f2[i]*b*(((zk1[i]*f2[i]-zk1[i-1]*f2[i-1])/(F2[i]-F2[i-1]))-((zk1[i+1]*f2[i+1]-zk1[i]*f2[i])/(F2[i+1]-F2[i])));
A[i+2][2] = A[2][i+2];
}

/*Second partial derivative of cell ai+1 to ai+2*/
for(int i=2;i<=n2;i++){
A[i+1][i+2] = -((r2i*(pow(b,2))*f2[i]*f2[i-1])/(F2[i]-F2[i-1]))-((r1i*f1[i]*f1[i-1])/(F1[i]-F1[i-1]));
A[i+2][i+1] = A[i+1][i+2];
}


float **Ainv;/*Inverse matrix of A*/
Ainv = matrix(1,n2+2,1,n2+2);

matrixinv(A,n2+2,Ainv);/*Inversion of the matrix A*/


 if (counterp == 200){
  fprintf(fp1,"A maximum of 200 iterations were reached. Convergence not reached \n");
 }

 else if (counterp == 0){
   //If convergence reached in 1st iteration
   AUC = normscum(a1/sqrt(1+pow(b1,2)));
   dabbaA = norms(a1/sqrt(1+pow(b1,2)))*(1/sqrt(1+pow(b1,2)));
   dabbaB = norms(a1/sqrt(1+pow(b1,2)))*a1*b1*(1/pow((1+pow(b1,2)),1.5f));
   VAUC = (pow(dabbaA,2) *Ainv[1][1]) + (pow(dabbaB,2)*Ainv[2][2])-(2*dabbaA*dabbaB*Ainv[1][2]);
   
   fprintf(fp1,"%lf," ,theta1[1]); //***Value for a ***
   fprintf(fp1," %lf," ,theta1[2]); //***Value for b ***
 for(int i=1; i<=n2;i++){
   fprintf(fp1,"%lf,",theta1[i+2]); //***Value for Zk**
   }
   fprintf(fp1,"%lf," ,AUC); //***Value for area under the curve (AUC)***
   fprintf(fp1,"%lf" ,VAUC); //***Value for the variance of area under the curve (AUC)***
   fprintf(fp1,"\n");
   }
 else{
   AUC = normscum(a/sqrt(1+pow(b,2)));
   dabbaA = norms(a/sqrt(1+pow(b,2)))*(1/sqrt(1+pow(b,2)));
   dabbaB = norms(a/sqrt(1+pow(b,2)))*a*b*(1/pow((1+pow(b,2)),1.5f));
   VAUC = (pow(dabbaA,2) *Ainv[1][1]) + (pow(dabbaB,2)*Ainv[2][2])-(2*dabbaA*dabbaB*Ainv[1][2]);
 
   fprintf(fp1,"%lf," ,theta4[1]);//***Value for a ***
   fprintf(fp1,"%lf," ,theta4[2]);//***Value for b ***
  for(int i=1; i<=n2;i++){
   fprintf(fp1,"%lf,",theta4[i+2]);//***Value for Zk**
  }
  fprintf(fp1,"%lf," ,AUC);//***Value for area under the curve (AUC)***
  fprintf(fp1,"%lf" ,VAUC);//***Value for the variance of area under the curve (AUC)***
  fprintf(fp1,"\n");
  }
   free_nrvector(r2,1,n1);
   free_nrvector(r1,1,n1);
   free_matrix(p,1,n1,1,2);
   free_nrvector(izk1,1,n2);
   free_nrvector(izk2,1,n2);
   free_nrvector(phi1,1,n2);
   free_nrvector(phi2,1,n2);
   free_nrvector(theta1,1,n2+2);
   free_nrvector(theta2,1,n2+2);
   free_nrvector(theta3,1,n2+2);
   free_nrvector(theta4,1,n2+2);
   free_nrvector(thetadif,1,n2+2);
   free_nrvector(zk1,1,n2);
   free_nrvector(F1,0,n1);
   free_nrvector(f1,0,n1);
   free_nrvector(F2,0,n1);
   free_nrvector(f2,0,n1);
   free_matrix(A,1,n2+2,1,2+2);
   free_matrix(Ainv,1,n2+2,1,2+2);
       } 
 
return 0;

  }














