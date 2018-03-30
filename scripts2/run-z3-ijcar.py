#!/usr/bin/python

import sys
import subprocess
from time import *

class Global:
  def __init__(self, file_with_names):
    self.filename_file="/home/jaideep/fpa-heterogeneous/decision-procedure/abstraction/code/data/"+file_with_names#shortlist.txt#files.txt#target-files.txt"#sort-uniq.txt"#"/home/jaideep/filenames.txt" #contains list of smt2 input filenames
    self.root = '/home/jaideep/fpa-heterogeneous/decision-procedure/abstraction/code/'
    self.bm_root = self.root+'misc/benchmarks/z3-ijcar/' 
    self.timeout = 1200#20 min per call 
    self.z3 = '/home/jaideep/tools/z3-ijcar/z3-39a8c79f68e0cf8322dc5f4d373bfbf027d5d26b/build/z3' #z3 

def main(argv):
 gd = Global(argv[1])
 filenames = open(gd.filename_file,"r") 
 succeeded = 0; failed = 0
 
 for filename in filenames:
   filename = filename.strip()
   #if(0 != filename.find("e")):
   #  continue
   print "Running on "+filename
   #if("add_01_1000_4.smt2"!=filename):
   #  continue
   try:
     #fixedpoint.print_answer=true
     t1 = time()
     output = subprocess.check_output(('time','timeout', str(gd.timeout), gd.z3, '-smt2', gd.bm_root+filename.strip()), stderr=subprocess.STDOUT)
     t2 = time()
     print output
     print "Time taken: "+str(t2-t1)
     succeeded = succeeded + 1
     #if(succeeded >= 20):
     #  break
   except subprocess.CalledProcessError as e:
     failed = failed + 1
     if (124 == e.returncode):#check for timeout
       #t2 = time()
       #print "Time taken: "+str(t2-t1)
       print "Run on "+filename.strip()+" returned timed out, subprocess.calledProcessError!"
       print e.output
     else:
       print "Run on "+filename.strip()+" returned with error, subprocess.calledProcessError!"
       print e.output
       #exit(1)
     #print e
   except:
     failed = failed + 1
     print "Run on "+filename.strip()+ " returned with error"
     print "Unexpected error:", sys.exc_info()[0]
 filenames.close()
 print "Returned normally on " +str(succeeded)+ " files" 
 print "Returned with exception on " + str(failed)+ " files"
sys.stdout.flush()
sys.stderr.flush()

if __name__=="__main__":
  main(sys.argv)
