#include<stdio.h>
#include<stdlib.h>
double convert_to_fp(unsigned int mantissa){
 // mantisaa = mantissa << 9;
 // convert 1.mantissa to decimal value by a loop 
 // multiplying by powers of 2, starting with 1.0
 return 1.0;
}
//assumes value is represnetable as a normalized value
int main(){
 unsigned int in = 1070141403;
 unsigned int *ptr = NULL;
 ptr = &in;
 if(4 != sizeof(unsigned int)){
  printf("Size of unsigned int is not 4!\n");
  exit(1);
 }
 printf("%u\n",*ptr);
 unsigned int sign = (0x80000000 & (*ptr))>>31;
 printf("%u\n",sign);
 unsigned biased_exponent = (0x7F800000 &(*ptr))>>23;
 unsigned exponent = biased_exponent - 127;
 printf("Unbiased exponent %u\n",exponent);
 unsigned mantissa = (0x007FFFFF &(*ptr));
 printf("%u\n",mantissa);
 //double fp_val;//ideally an rational type
 //fp_val = pow(-1.0,sign)* convert_to_fp(mantissa) * pow(2.0,exponent);//try using just bits
 return 0;
}
