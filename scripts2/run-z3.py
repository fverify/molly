#!/usr/bin/python

import sys
import subprocess
from time import *

class Global:
  def __init__(self, filename):
    self.filename_file = "/home/jaideep/repositories/fpa-heterogeneous/decision-procedure/abstraction/code/data/"+filename #contains list of smt2 input filenames
    self.ignore_filename_file = "/home/jaideep/repositories/fpa-heterogeneous/decision-procedure/abstraction/code/data/mathsat-to.txt"
    self.root = "/home/jaideep/repositories/fpa-heterogeneous/decision-procedure/abstraction/code/"
    self.bm_root = self.root+'examples/polynomials/smt2/for-numerical/z3/'#'misc/benchmarks/converted/'#'examples/polynomials/smt2/'#'misc/benchmarks/converted/' 
    self.timeout = 600# 10 min per call, 20 min per call 

def main(argv):
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
 for filename in filenames:
   #if(0 != filename.find("e")):
   #  continue
   print "Running on "+filename.strip()
   #if("e2_2.c.smt2"!=filename):
   #  continue
   if (filename.strip() in ignore_list):
     print "Run on "+filename.strip()+" returned timed out, subprocess.calledProcessError!"
     sys.stdout.flush()
     continue
   #continue
   filename = filename.strip()
   sys.stdout.flush()
   try:
     t1 =  time()
     #output = subprocess.check_output(('timeout', str(gd.timeout), 'mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=1','-theory.fp.bit_blast_mode=1','-model',gd.bm_root+filename.strip()), stderr=subprocess.STDOUT)
     output = subprocess.check_output(('timeout', str(gd.timeout), 'z3', '-smt2', 'dump_models=true', gd.bm_root+filename.strip()), stderr=subprocess.STDOUT)
     t2 = time()
     print output
     print "Time taken: "+str(t2-t1)
     succeeded = succeeded + 1
     #if(succeeded >= 20):
     #  break
   except subprocess.CalledProcessError as e:
     failed = failed + 1
     if (124 == e.returncode):#check for timeout
       print "Run on "+filename.strip()+" returned timed out, subprocess.calledProcessError!"
     else:
       print "Run on "+filename.strip()+" returned with error, subprocess.calledProcessError!"
       print e
       #exit(1)
     #print e
   except:
     failed = failed + 1
     print "Run on "+filename.strip()+ " returned with error"
     print "Unexpected error:", sys.exc_info()[0]
 filenames.close()
 ignore_filenames.close()
 print "Returned normally on " +str(succeeded)+ " files" 
 print "Returned with exception on " + str(failed)+ " files"

if __name__=="__main__":
  main(sys.argv)
