#include<stdio.h>
#include<stdlib.h>
//assumes value is representable as a normalized value
int main(){
 unsigned int in;
 scanf("%u",&in);
 //in = 0x07fff76f;
 //printf("%u\n",in);
 void* ptr = &in;
 float *fptr = (float*)ptr;
 printf("%6.170f\n",*fptr);
 //printf("%0x\n",in);
 return 0;
}
