#!/usr/bin/python

import sys
import subprocess
from time import *

class Global:
  def __init__(self, filename, suite):
    self.filename_file="/home/jaideep/repositories/fpa-heterogeneous/decision-procedure/abstraction/code/data/"+filename#shortlist.txt" #newton/newton-list.txt"#filenames-zoom-in.txt" #contains list of smt2 input filenames #"/Users/jaideep/repos/May29/fpa-heterogeneous/decision-procedure/abstraction/code/data/"+filename
    #/Users/jaideep/repos/May29/fpa-heterogeneous/decision-procedure/abstraction/code/data/"+filename
    self.root ='/home/jaideep/repositories/fpa-heterogeneous/decision-procedure/abstraction/code/'# '/Users/jaideep/repos/May29/fpa-heterogeneous/decision-procedure/abstraction/code/'
    if(0 == int(suite)):
      self.bm_root = self.root+'misc/benchmarks/griggio/'#'examples/polynomials/fml/'#'misc/benchmarks/griggio/'#self.root+'newton/' #self.root+'misc/benchmarks/griggio/'
    else:
      self.bm_root = self.root+'examples/polynomials/fml/'#'examples/polynomials/fml/'#'misc/benchmarks/griggio/'#self.root+'newton/' #self.root+'misc/benchmarks/griggio/'
    self.timeout = 1200#20 min per call

def main(argv):
 gd = Global(argv[1], argv[2])
 filenames = open(gd.filename_file,"r")
 succeeded = 0; failed = 0; timed_out = 0
 exception_files = []
 timed_out_files = []

 for filename in filenames:
   filename = filename.strip()
   #if(0 != filename.find("e")):
   #  continue
   print "Running on "+filename
   try:
     t1 = time()
     print gd.root
     print gd.bm_root
     print gd.bm_root+filename.strip()
     if(0 == int(argv[2])):
       #output = subprocess.check_output(('timeout',str(gd.timeout),gd.root+'solve_rp.py', gd.bm_root+filename.strip(),'lfp'), stderr=subprocess.STDOUT)
       output = subprocess.check_output(('timeout', str(gd.timeout), gd.root+'solve_rp.py','-a','real','-smt2',gd.bm_root+filename.strip()), stderr=subprocess.STDOUT)
       #i#output = subprocess.check_output(('timeout', str(gd.timeout), gd.root+'solve_rp.py','-gb','-gbr','-a','real','-smt2', gd.bm_root+filename.strip()), stderr=subprocess.STDOUT)
     else:
       #output = subprocess.check_output(('timeout',str(gd.timeout), gd.root+'solve_rp.py','-a','approx','-cfg','examples/single-prec-modified2.cfg','-fml',gd.bm_root+filename.strip().rstrip("smt2")+"fml"), stderr=subprocess.STDOUT)
       output = subprocess.check_output(('timeout',str(gd.timeout), gd.root+'solve_rp.py','-a','lfp','-cfg','examples/single-prec-modified2.cfg','-fml',gd.bm_root+filename.strip().rstrip("smt2")+"fml"), stderr=subprocess.STDOUT)
       #output = subprocess.check_output(('timeout',str(gd.timeout), gd.root+'solve_rp.py','-gb','-gbd','-a','real','-cfg','examples/single-prec-modified2.cfg','-fml',gd.bm_root+filename.strip().rstrip("smt2")+"fml"), stderr=subprocess.STDOUT)
       #output = subprocess.check_output(('timeout',str(gd.timeout),gd.root+'solve_rp.py', gd.bm_root+filename.strip().rstrip("smt2")+"fml",'examples/single-prec-modified2.cfg','lfp'),stderr=subprocess.STDOUT)#'examples/single-prec-modified2.cfg','lfp'), stderr=subprocess.STDOUT)
     t2 = time()
     print output
     print "Time taken: "+str(t2 - t1)
     succeeded = succeeded + 1
     #if(succeeded >= 20):
     #  break
   except subprocess.CalledProcessError as e:
     failed = failed + 1
     if (124 == e.returncode):#check for timeout
       timed_out = timed_out + 1
       print "Run on "+filename.strip()+" returned timed out, subprocess.calledProcessError!"
       timed_out_files+=[filename]
     else:
       print "Run on "+filename.strip()+" returned with error, subprocess.calledProcessError!"
       exception_files+=[filename]
     #print e
   except:
     failed = failed + 1
     exception_files+=[filename]
     print "Run on "+filename.strip()+ " returned with error"
     print "Unexpected error:", sys.exc_info()[0]
 filenames.close()
 print "Returned normally on " +str(succeeded)+ " files"
 print "Returned with exception on " + str(failed)+ " files"
 print "Out of the files with exception, number that timed out: "+str(timed_out)
 print "Files that timed out: "
 print timed_out_files
 print "Files that returmed exception or error: "
 print exception_files

if __name__=="__main__":
  main(sys.argv)
