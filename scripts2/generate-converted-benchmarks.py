#!/usr/bin/python

import sys
import subprocess

class Global:
  def __init__(self):
    self.root = '/home/jaideep/repositories/fpa-heterogeneous/decision-procedure/abstraction/code/'
    self.filename_file=self.root+'filenames.txt' #contains list of smt2 input filenames
    self.bm_root = self.root+'misc/benchmarks/griggio/'
    self.timeout = 1200#20 min per call

def main(argv):
 gd = Global()
 filenames = open(gd.filename_file,"r")
 succeeded = 0; failed = 0

 for filename in filenames:
   filename = filename.strip()
   #if(0 != filename.find("e")):
   #  continue
   print "Running on "+filename
   try:
     #output = subprocess.check_output(('timeout',str(gd.timeout),gd.root+'solve.py', gd.bm_root+filename.strip(),'lfp'), stderr=subprocess.STDOUT)
     output = subprocess.check_output((gd.root+'solve_rp.py', gd.bm_root+filename.strip(),'lfp'), stderr=subprocess.STDOUT)
     print output
     succeeded = succeeded + 1
     #if(succeeded >= 20):
     #  break
   except subprocess.CalledProcessError as e:
     failed = failed + 1
     if (124 == e.returncode):#check for timeout
       print "Run on "+filename.strip()+" returned timed out, subprocess.calledProcessError!"
     else:
       print "Run on "+filename.strip()+" returned with error, subprocess.calledProcessError!"
     #print e
   except:
     failed = failed + 1
     print "Run on "+filename.strip()+ " returned with error"
     print "Unexpected error:", sys.exc_info()[0]
 filenames.close()
 print "Returned normally on " +str(succeeded)+ " files"
 print "Returned with exception on " + str(failed)+ " files"

if __name__=="__main__":
  main(sys.argv)
