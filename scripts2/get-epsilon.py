#!/usr/bin/python

import sys
import subprocess
from time import *

class Global:
  def __init__(self, filename):
    self.epsilon = 0.0001
    self.filename_file = "/home/jaideep/repositories/fpa-heterogeneous/decision-procedure/abstraction/code/data/"+filename #contains list of smt2 input filenames
    self.ignore_filename_file = "/home/jaideep/repositories/fpa-heterogeneous/decision-procedure/abstraction/code/data/mathsat-to.txt"
    self.root = "/home/jaideep/repositories/fpa-heterogeneous/decision-procedure/abstraction/code/"
    self.bm_root = self.root+'examples/polynomials/'#'misc/benchmarks/converted/' 
    self.eps_root = self.bm_root+'range-epsilon/'
    self.bound1 = 10 
    self.bound2 = 60
    self.bound3 = 300
    self.timeout = 1200#
    self.bm_timeout = 3600 

def write_initial_epsilon(gd, filename, epsilon,addition, to_be_replaced, replacement2):
  result_str= ""
  f1=open(gd.bm_root+filename,"r")
  for line in f1:
    result_str+=line
  f1.close()
  result_str = result_str.replace(to_be_replaced, replacement2)
  result_str = addition+str(epsilon)+"))\n"+result_str
  f2=open(gd.eps_root+filename,"w")
  f2.write(result_str)
  f2.close()

def replace_epsilon(gd, filename, search, epsilon):
  result_str = ""
  f1=open(gd.eps_root+filename,"r")#in read-only mode
  for line in f1:
    if(-1 != line.find(search)):
      result_str+=search+str(epsilon)+"))\n"
    else:
      result_str+=line
  f1.close()
  f2=open(gd.eps_root+filename,"w")#in write mode
  f2.write(result_str)
  f2.close()
  return ""


def main(argv, solver):
 gd = Global(argv[1])
 filenames = open(gd.filename_file,"r") 
 succeeded = 0; failed = 0 
 ignore_filenames = open(gd.ignore_filename_file,"r")
 #print "Ignoring"
 #print ignore_filenames
 #for filename in ignore_filenames:
 # print filename.strip()
 #exit(1)
 ignore_list = []
 #ignore_list = ['div2.c.40.smt2','div2.c.50.smt2','div3.c.10.smt2','div3.c.20.smt2','div3.c.30.smt2','div3.c.3.smt2','div3.c.40.smt2','div3.c.50.smt2','div.c.10.smt2','div.c.20.smt2','div.c.30.smt2','div.c.3.smt2','div.c.40.smt2','div.c.50.smt2','gaussian.c.175.smt2','gaussian.c.25.smt2','gaussian.c.75.smt2']
 addition = "(define-fun epsilon () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN "#+"))" needs to append the actual value and then the two close parens
 search = addition
 to_be_replaced = "(fp.gt arithexp const0)"
 replacement2 = "(fp.gt arithexp epsilon)"
 for filename in filenames:
   #if(0 != filename.find("e")):
   #  continue
   print "##########Running on "+filename.strip()+"##########"
   sys.stdout.flush()
   #if("e2_2.c.smt2"!=filename):
   #  continue

   if (filename.strip() in ignore_list):
     print filename.strip()+" is on ignore list"
     sys.stdout.flush()
     continue
   #continue
   filename = filename.strip()
   sys.stdout.flush()
   range1_epsilon_found = False
   range2_epsilon_found = False
   range3_epsilon_found = False
    
   # LEARNING BOUNDS PHASE
   tstart = time()
   lower = 0
   epsilon = gd.epsilon#0.001
   upper = 10.0#initialized to a high arbitrary value
   lower_found = False; upper_found = False;
   write_initial_epsilon(gd, filename,epsilon, addition, to_be_replaced, replacement2)
   #exit(0)
   titer = time() - tstart
   while((titer <= gd.bm_timeout) and (lower <= upper)):# and (not (lower_found and upper_found))):
     print "Time since start of the learning bounds phase is "+str(titer)
     print "Current lower = "+str(lower)+" Current upper = "+str(upper)+ " epsilon = "+str(epsilon)
     sys.stdout.flush()
     replace_epsilon(gd, filename, search, epsilon)
     try:
       print "Starting a new iteration for file "+filename+" with epslion = "+str(epsilon)
       #substitute for epsilon
       t1 =  time()
       if("MATHSAT" == solver):
         #output = subprocess.check_output(('timeout', str(gd.timeout), 'mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=1','-theory.fp.bit_blast_mode=1','-model',gd.eps_root+filename.strip()), stderr=subprocess.STDOUT)
         output = subprocess.check_output(('timeout', str(gd.timeout), 'mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=0','-theory.fp.bit_blast_mode=1','-model',gd.eps_root+filename.strip()), stderr=subprocess.STDOUT)
       #output = subprocess.check_output(('timeout', str(gd.timeout), 'mathsat','-printer.fp_number_format=1','-model',gd.eps_root+filename.strip()), stderr=subprocess.STDOUT)
       else:
         output = subprocess.check_output(('timeout', str(gd.timeout), 'z3','-smt2',gd.eps_root+filename.strip()), stderr=subprocess.STDOUT)
       t2 = time()
       print output
       time_taken = t2 - t1
       print time_taken
       if((output[0:5]=="unsat")):
         print "Formula unsat for "+filename+" with epsilon = "+str(epsilon)
         upper = epsilon; upper_found = True; 
         if(True == lower_found):
           epsilon = (lower + upper)/2.0
         else:
           epsilon = epsilon/2.0;
       elif((output[0:6]=="(error")):
         print "Error when "+filename+" called with epsilon = "+str(epsilon)
         exit(1)
       elif(time_taken <= gd.bound1):
         print "Formula sat in "+str(time_taken)+" seconds for "+filename+" with epsilon = "+str(epsilon)
         lower= epsilon; lower_found = True
         if(True == upper_found):
           epsilon = (lower + upper)/2.0
         else:
           epsilon = epsilon * 2.0;
       elif(time_taken <= gd.bound2):
         range1_epsilon_found = True
         print "Lower-range epsilon found; Formula sat in "+str(time_taken)+" seconds for "+filename+" with epsilon = "+str(epsilon)
         lower= epsilon; lower_found = True
         if(True == upper_found):
           epsilon = (lower + upper)/2.0
         else:
           epsilon = epsilon * 2.0;
       elif(time_taken <= gd.bound3):
         range2_epsilon_found = True
         print "Mid-range epsilon found; Formula sat in "+str(time_taken)+" seconds for "+filename+" with epsilon = "+str(epsilon)
         lower= epsilon; lower_found = True
         if(True == upper_found):
           epsilon = (lower + upper)/2.0
         else:
           epsilon = epsilon * 2.0;
       elif(time_taken<=gd.timeout):
         range3_epsilon_found = True
         #print "SUCCESS, for "+filename+" with epsilon = "+str(epsilon)+" "
         print "High-range epsilon found; Formula sat in "+str(time_taken)+" seconds for "+filename+" with epsilon = "+str(epsilon)
         print "lower = "+str(lower)+" upper = "+str(upper)+ " epsilon = "+str(epsilon)
         titer = time() - tstart
         #break
       else:
         print "else condition: error?"
         exit(1)
       print "Time taken: "+str(t2-t1)
       if((range1_epsilon_found and range2_epsilon_found) and range3_epsilon_found):
         succeeded = succeeded + 1
		   #if(succeeded >= 20):
         break
       titer = time() - tstart
       print "Titer: "; print titer
     except subprocess.CalledProcessError as e:
       failed = failed + 1
       if (124 == e.returncode):#check for timeout
         print "Run on "+filename.strip()+" with epsilon "+" returned timed out, subprocess.calledProcessError!"
         upper = epsilon; upper_found = True
         if(True == lower_found):
           epsilon = (lower + upper)/2.0
         else:
           epsilon = epsilon/2.0;
       else:
         print "Run on "+filename.strip()+" returned with error, subprocess.calledProcessError!"
         print e
         #exit(1)
         #print e
       titer = time() - tstart
     except:
       failed = failed + 1
       print "Run on "+filename.strip()+ " returned with error"
       print "Unexpected error:", sys.exc_info()[0]
       #exit(1)
   #SEARCHING WITHIN THE BOUNDS PHASE
 filenames.close()
 ignore_filenames.close()
 print "Returned normally on " +str(succeeded)+ " files" 
 print "Returned with exception on " + str(failed)+ " files"

if __name__=="__main__":
  #main(sys.argv, "Z3")
  main(sys.argv, "MATHSAT")
