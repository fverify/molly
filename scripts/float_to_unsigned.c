#include<stdlib.h>
#include<stdio.h>
//          0.0000000000000000000000000000000000000235098814112518954702282342489363910808264297170130052045776503248818287333847949014781418924417374406721226165473126457072794437408447265625
int main(){
 //float a1 = 0.000000000000000000000000000000000000011754943508222875079687365372222456778186655567720875215087517062784172594547271728515625;
 //float a2 = 0.000000000000000000000000000000000000011754943508222875079687365372222456778186655567720875215087517062784172594547271728515625;
 //float a3 = 0.0000000000000000000000000000000000000235098842138488215097405888969857469765410485749178666771434906114317774095123780853100470267236232757568359375;
 //float a4 = 0.0000000000000000000000000000000000007052966104933725047812419223333474066911993340632525129052510237670503556728363037109375;
 float delta = 0.025;
 float a1 = 0.000000000000000000000000000000000000011754943508222875079687365372222456778186655567720875215087517062784172594547271728515625;
 float a2 = 0.0000000000000000000000000000000000000235098814112518954702282342489363910808264297170130052045776503248818287333847949014781418924417374406721226165473126457072794437408447265625;
 float a3 = 0.0000000000000000000000000000000000000117549463108198037293215072196816233580189181282447589681190605769207403741294371002368279732763767242431640625;
 float a4 = 0.0000000000000000000000000000000000000117549463108198037293215072196816233580189181282447589681190605769207403741294371002368279732763767242431640625;
 float lower = 0.000000000000000000000000000000000000011754943508222875079687365372222456778186655567720875215087517062784172594547271728515625;
 float nlower = -0.000000000000000000000000000000000000011754943508222875079687365372222456778186655567720875215087517062784172594547271728515625;
 float upper = 1024.0;
 float nupper = -1024.0;
 printf("Size of unsigned  = %ld\n",sizeof(unsigned int));
 unsigned int* ptr1 = NULL;
 unsigned int* ptr2 = NULL;
 unsigned int* ptr3 = NULL;
 unsigned int* ptr4 = NULL;
 unsigned int* ptr5 = NULL;
 unsigned int* ptr6 = NULL;
 unsigned int* ptr7 = NULL;
 unsigned int* ptr8 = NULL;
 unsigned int* ptr9 = NULL;
 //ptr1 = ptr2 = ptr3 = ptr4 = NULL;
 ptr1 = (void*)&a1; 
 ptr2 = (void*)&a2; 
 ptr3 = (void*)&a3; 
 ptr4 = (void*)&a4; 
 ptr5 = (void*)&upper; 
 ptr6 = (void*)&lower;
 ptr7 = (void*)&nlower;
 ptr8 = (void*)&nupper;
 ptr9 = (void*)&delta;
 printf("a1=%u, a2=%d, a3=%d, a4=%d, upper = %d, lower = %d, nlower = %u, nupper = %u,delta = %u\n",*ptr1,*ptr2,*ptr3,*ptr4,*ptr5,*ptr6,*ptr7,*ptr8,*ptr9); 
 return 0;
}