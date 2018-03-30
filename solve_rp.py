#!/usr/bin/python2.7
##!/sw/bin/python2.7 # for Mac
# Purpose: Decide a floating-point formula (in canonical form)


from gmpy2 import *#better practice: just import module
import gmpy2
import string, warnings
from fractions import Fraction
import sys, subprocess
#from time import ctime
from time import *
import os, re
import platform
#import sys,re
from collections import OrderedDict
#import solve
#from lifting_policies import *
import operator
import argparse

class GlobalData:
  def __init__(self):
    self.var_selection_policy = 4 # 0 = select one var heuristically to invert one prop; 1 =  select every variable all at once, to invert/maintain all; 2 = select one variable, either JUST ONE or ALL one after the other in no particular order [order in which the names as keys in dict get displayed] to invert/maintain all; 3 (optional) = select every variable, one after the other to invert at least one invertible; 4 = select based on a ranking (say based on highest degree in an invertible), JUST ONE or ALL one after the other to invert/maintain all;  5 = select every variable that OCCURS in at least one INVERTIBLE, all at once, to invert/maintain all;
    self.select_all_vars_in_sequence = True #default(False): select only the top ranked variable
    self.reverse_ranked_vars = False #default(False): lowest degree first
    self.enable_delta_bounds = False
    self.bound = '0.05'
    self.generate_benchmark = False #generate formula being solved (slightly diff from original formula) in the SMT-LIB2 format (format slightly diff from input format)
    self.generate_benchmark_real = False
    self.generate_benchmark_dreal = False
    self.enable_abstract_check = False# abstract value check, as well as fp value check
    self.enable_final_fp_check = True #enable fp value check
    self.enable_strict_consis_check = False
    self.enable_only_normal = True
    self.enable_only_normal_var = True
    self.enable_only_normal_arithexp = True
    self.enable_only_normal_delta = False
    self.no_lifting = False #default: False to enable lifting
    self.checking_phase = False #is it the phase where an FP assignment is being checked wrt original formula
    self.input_filename = ""
    self.cfg_filename = "Empty"
    self.error_filename = "error_solve.txt"
    self.summary_filename = "summary.txt"
    self.lift_app = "lift_stats.txt"
    self.start_time = time()
    self.iteration = 1 #iteration count
    self.abstraction = "lfp" #"real" #"lfp" for reducded precision abstraction or "real" or "approx"
    #self.approx = True # True if using an approximate proxy solver, like dReal
    self.precision = 3 #initial abstract precision when lfp
    self.max_precision = 23 #hardcoded for now for single prec
    self.refine_prec_inc = 3 #hardcoded for now
    self.exponent = 3 #initial abstract exponent when lfp
    self.max_exponent = 8 #hardcoded for now for single prec
    self.refine_exp_inc = 1 #hardcoded for now, default increase in exponent per iteration
    self.avars = {}
    self.consts = {}
    self.arithexps = {}
    self.props = {}
    self.relexps = {}
    self.propexps = {}
    self.asserts = {}
    self.new_asserts = {}
    self.ignore_asserts = {}
    self.new_index = 0
    self.ordered=OrderedDict() #maintains all Vars, Consts, ArithExps, Props, PropExps in the ordered read in the input SMT2 file
    self.initialization =  ""
    self.simplify_index = 0
    self.overall_timeout = "1200" # TO for the tool MOLLY
    self.outer_timeout = "900" # 360 180     360 (outer) abstract solving time out
    self.inner_timeout = "60" #240(60) 720 (inner) exact solving time out
    self.tmin_lift = "10"
    #for adaptive refinement
    #dictionaries with relevant data about all previous iterations
    self.iter_result = {} #dictionary that maintains the abstract solving result for each of the earlier iterations: {<iter#>:<result>, ...}
    self.iter_time_taken = {} #dictionary that maintains the solving time for each of the earlier iterations: {<iter#>:<time>, ...}
    self.iter_precision = {} #dictionary that maintains precision for each of the earlier iterations: {<iter#>:<precision>, ...}
    self.iter_exponent = {} #dictionary that maintains exponent for each of the earlier iterations: {<iter#>:<exponent>, ...}
    self.delta_obtained = False
    self.molly_debug_file = "molly_debug.txt"
    self.try_own_assignment = False
    self.non_symbolic_model_lift = False
    self.local_search_exp_factor_str = '2'
    self.smallest_norm_pos_single_prec_str = '0.0000000000000000000000000000000000000117549435082228750796873653722224567781866555677208752150875170627841725945472717285156250'

  def increment_simplify_index(self):
    self.simplify_index+=1

  def generate_smtlib_fp(self):
    constraint = ""
    if(self.abstraction == "approx"):#self.generate_benchmark_dreal
      constraint+="(set-logic QF_NRA)\n"
    for obj in self.ordered.keys():
      constraint += obj.print_one_smtlib_stmt(self)+"\n"
    return constraint

  def increment_index(self):
    self.new_index+=1

def print_final(gd):
  myprint("Molly terminating\n")
  exit(0)

def print_error_msg(gd,msg):
  ferr = open(gd.error_filename,"a")
  ferr.write(gd.input_filename+msg)
  ferr.flush()
  ferr.close()

def PRINT_DEBUG(gd,x):
  #print (x)
  gd.initialization+=x+"\n"

#gd = GlobalData()
def rename(original):
  return "lit_"+original.lstrip(".")

def rename_new(original,gd):
  return original+"_new"+str(gd.new_index)

def rank(propexp, inv_arith_vars):
  inv_arith_vars_dict = {}
  for var in inv_arith_vars:
    inv_arith_vars_dict[var] = propexp.deg(var)

  ranked_var_tuples = sorted(inv_arith_vars_dict.items(), key=operator.itemgetter(1))
  ranked_var_list = [v[0] for v in ranked_var_tuples]
  for var in ranked_var_list:
    print var.name+" : "+ str(inv_arith_vars_dict[var])
    frank.write(var.name+" : "+ str(inv_arith_vars_dict[var])+"\n")
  #exit(0)
  return ranked_var_list #inv_arith_vars

def parse(line,gd):
  #global gd
  #PRINT_DEBUG(gd,"Inside parse function")
  if((";"==line[0])or(line=='\n')):
    return
  elif(-1!=line.find("(set-logic QF_FPABV)")):
    return
  #check for
  elif(-1!=line.find("(define-fun .3 () RoundingMode roundNearestTiesToEven)")):
    return
  elif (-1!=line.find("declare-fun |goto_symex::&92;")):
    #PRINT_DEBUG(gd,"Ignoring the strange goto_symex...")
    return
  elif((-1!=line.find("(_ asFloat ")) and (-1!=line.find("roundT"))):#a constant number
    toks = line.split(" ")
    name = rename(toks[1])
    #PRINT_DEBUG(gd,"Constant "+name)
    sign=""
    if("-" in toks[-2]):
      sign="-"
    constant_value=sign+(toks[-1].rstrip("\n").replace(")",""))
    gd.consts[name]=name
    gd.ordered[name]=name
    #string=name
    PRINT_DEBUG(gd,name.strip()+"=Const(mpfr('"+constant_value.strip()+"'),Fraction('"+constant_value.strip()+"'))")
    #PRINT_DEBUG(gd,name+"=Const("+name+",mpfr('"+constant_value+"'),Fraction('"+constant_value)#+"')")
    #PRINT_DEBUG(gd,constant_value)
  elif(-1!=line.find("(declare-fun")):#check for arithmetic variables
    name = rename(line.split(" ")[1])
    comment_out = ""
    if(-1!=line.find("main::")):# if the arith var is that wierd one with main::, ignore
      comment_out = "#"
    else:
      gd.avars[name] = name
      gd.ordered[name]=name
    PRINT_DEBUG(gd,comment_out+name+" = Var('"+name+"')")
  elif(-1!=line.find("(define-fun ")):#check for arithmetic expressions:
    #search_str = "() (_ FP "
    #offset = len(search_str)
    #if(-1!=(index= line.find(search_str)):
    #  ileft=line[index+offset].find()
    matched = re.search('\([+\-\*/]',line)
    if(None!=matched):
      aexp = line[matched.start()+1:line.find("))")]
      #PRINT_DEBUG(gd,"Arithmetic expression: ")
      #PRINT_DEBUG(gd,aexp)
      lhs = rename(line.split(" ")[1])
      gd.arithexps[lhs]=lhs
      gd.ordered[lhs]=lhs
      toks = aexp.split(" ")
      if('-'==toks[0]and (len(toks)<4)):#Arithmetic expression with a unary minus '-'
        #negated_const = "-"+toks[1]
        #PRINT_DEBUG "Const(mpfr('"+negated_const+"'),Fraction(str(mpfr('"+negated_const+"'))))"
        #check if constant -1 is already declared
        # if not declare it and use it
        if (not("lit_const_minus_1" in gd.consts.keys())):
          gd.consts["lit_const_minus_1"] = "lit_const_minus_1"
          gd.ordered["lit_const_minus_1"]="lit_const_minus_1"
          PRINT_DEBUG(gd,"lit_const_minus_1 = Const(mpfr('1'),Fraction('1'))")
        PRINT_DEBUG(gd,lhs+"=ArithExp(lit_const_minus_1,'*',"+rename(toks[1])+")")
        #Const(mpfr('1'),Fraction(str(mpfr('1'))))
      else:#binary arithmetic expression
        PRINT_DEBUG(gd,lhs+"=ArithExp("+rename(toks[2])+",'"+toks[0]+"',"+rename(toks[3])+")")
  #(define-fun .12 () (_ FP 8 24) (* .3 .9 .9))
    elif(-1==line.find(" Bool ")):#Expression does n't have +,-,*,/ and is not a regular RelExp; so just a simple assignment, a special kind of RelExp
      comment_out=""
      if(-1!=line.find("main::")):
         comment_out = "#"
      split_line=line.split(" ")
      opnd1=rename(split_line[1])
      opnd2=rename(split_line[-1].rstrip(")\n"))
      #declare the variables if not already declared
      if(not (opnd1 in gd.avars)):
        PRINT_DEBUG(gd,opnd1 + " = Var('"+opnd1+"'"+')')
        gd.avars[opnd1]=opnd1
        gd.ordered[opnd1]=opnd1
        #PRINT_DEBUG(gd,"\n\n")
        #PRINT_DEBUG(gd,opnd2+"=Var('"+opnd2+"'"+')')
      #generate prop name, relational exp name
      lhs=rename_new(opnd1,gd)#name of Prop
      gd.increment_index()
      relexp_name=lhs+"_rel" # name of RelExp
      #add prop, relational expression
      if("#"!=comment_out):
        gd.props[lhs]=lhs#add Prop
        gd.ordered[lhs]=lhs
        gd.relexps[relexp_name]=relexp_name#add RelExp
        gd.ordered[relexp_name]=relexp_name#add RelExp
        #PRINT_DEBUG(gd,"****")
        #PRINT_DEBUG(gd,relexp_name)
        #PRINT_DEBUG(gd,"****")
      string=comment_out+relexp_name
      string+=" = RelExp("
      string+=opnd1
      string+=",'=',"
      string+=opnd2
      string+=")"#define RelExp
      PRINT_DEBUG(gd,string)
      PRINT_DEBUG(gd,comment_out+lhs+"=Prop('"+lhs+"',"+relexp_name+")")#define Prop
      if("#"==comment_out):
        gd.ignore_asserts[lhs] = lhs
      else:
        gd.new_asserts[lhs] = lhs #adding this prop as an assertion
        gd.ordered[lhs] = lhs
  #either rel/prop (<,<=,>,>=,=) or propositional expression (not, and, or)
    if(-1!=line.find(" Bool ")):
      #PRINT_DEBUG(gd,"Found a Prop or PropExp")
      #sys.exit(1)
      toks=line.split(" ")
      lhs = rename(toks[1].rstrip(")"))
      #PRINT_DEBUG(gd,lhs)
      operator = toks[4].lstrip("(")
      if(operator in ['and','not','or']):#this is a propexp
        if(not (lhs in gd.propexps)):
          gd.propexps[lhs]=lhs
          gd.ordered[lhs]=lhs
        if('not'==operator):
            opnd=toks[5].rstrip("\n").rstrip(")")
            PRINT_DEBUG(gd,lhs+"=PropExp(gd,'"+lhs+"',"+rename(opnd)+",'not',None)")
        else:
            opnd2=toks[6].rstrip("\n").rstrip(")")
            PRINT_DEBUG(gd,lhs+"=PropExp(gd,'"+lhs+"'"+rename(toks[5])+",'"+operator+"',"+rename(opnd2)+")")
      elif(operator in ['<','<=','=','>','>=']):
        relexp_name = lhs+"_rel"
        #PRINT_DEBUG(gd,"relexp_name: "+relexp_name+"\n")
        if(not (lhs in gd.props.keys())):
          gd.props[lhs]=lhs
          gd.ordered[lhs]=lhs
          gd.relexps[relexp_name]=relexp_name
          gd.ordered[relexp_name]=relexp_name
        #PRINT_DEBUG(gd,"\n\n")
        opnd2=toks[6].rstrip("\n").rstrip(")")#[:-4]
        string=relexp_name#lhs.rstrip(")")
        string +="=RelExp("+rename(toks[5])+",'"+operator+"',"+rename(opnd2)+")"
        PRINT_DEBUG(gd,string)
        PRINT_DEBUG(gd,lhs+"=Prop('"+lhs+"',"+relexp_name+")")
  elif(-1!=line.find("(assert ")):
    name = rename(line.split(" ")[1].rstrip(")\r\n"))
    gd.asserts[name]=name
    gd.ordered[name]=name
  elif((-1!=line.find("check-sat"))or(-1!=line.find("(get-model)"))):
    return
  else:
    PRINT_DEBUG(gd,"Unhandled input constraint!")
  #PRINT_DEBUG(gd,"Hello: "+line)

def print_tokens(gd):
  PRINT_DEBUG(gd,"#ArithVars: ")
  PRINT_DEBUG(gd,"#"+str(gd.avars))
  PRINT_DEBUG(gd,"#Constants: ")
  PRINT_DEBUG(gd,"#"+str(gd.consts))
  PRINT_DEBUG(gd,"#ArithExps: ")
  PRINT_DEBUG(gd,"#"+str(gd.arithexps))
  PRINT_DEBUG(gd,"#RelExps: ")
  PRINT_DEBUG(gd,"#"+str(gd.relexps))
  PRINT_DEBUG(gd,"#Props: ")
  PRINT_DEBUG(gd,"#"+str(gd.props))
  PRINT_DEBUG(gd,"#PropExps: ")
  PRINT_DEBUG(gd,"#"+str(gd.propexps))
  PRINT_DEBUG(gd,"#Asserts: ")
  PRINT_DEBUG(gd,"#"+str(gd.asserts))
  PRINT_DEBUG(gd,"#Introduced Asserts: ")
  PRINT_DEBUG(gd,"#"+str(gd.new_asserts))
  PRINT_DEBUG(gd,"#Ignored Asserts: ")
  PRINT_DEBUG(gd,"#"+str(gd.ignore_asserts))
  PRINT_DEBUG(gd,"#Ordered Dict: ")
  PRINT_DEBUG(gd,"#"+str(gd.ordered))


#def generate_smtlib(gd):
#  lis = string(gd.ordered())
#  for lit in :
#    if(isinstance(lit,PropExp)):
#      print str(lit)+'='+str(lit.left_exp)+' '+str(lit.bool_op)+' '+str(lit.right_exp)
#    else:
#      print "Skipping "+str(lit)


def generate_constraint(lis,cons,brackets,n):
  if(1==n):
    return cons+str(lis[0])+brackets
  else:
    return generate_constraint(lis[1:],cons+"PropExp("+str(lis[0])+",'and',",brackets+")",n-1)


###########CONFIG options for this program
run_option = 1 #0 for demo run, 1 for regular run, 2 for regular run but with artificial initial assignment generation
# of initial assignment (artificially) using z3/Realizer
########### GLOBAL variables ############
TRANSLATOR_PATH = "bin/translator"
TRANSLATOR_CFG_FP = "examples/single-prec-modified2.cfg"
TRANSLATOR_CFG_MIXED ="examples/single-prec-modified2-mixed.cfg"
PARSER_GENERATOR_PATH = "bin/parser-generator"
BV_PARSER_GENERATOR_PATH = "./parser"
ARITH_VARS_FILE = "arith-vars.txt"
#LOGFILE="repeat-log-mathsat-negative-even.txt"
#flog=open(LOGFILE,"w")
DEBUG_LEVEL = 2
STATFILE="individual.txt"
RANKFILE="ranked_list.txt"
Z3_MIXED_TIMEOUT = 360
MATHSAT_DELTA_TIMEOUT = Z3_DELTA_TIMEOUT = 180
D_SOLVER="MATHSAT"
k = 20 # number of simples in the immediate neighbourhood
LEAST_NUM = "0.000000000000000000000000000000000000011754943508222875079687365372222456778186655567720875215087517062784172594547271728515625000" #This is the least normal(ized) single-precision number, constant for now: but actually depends on the specific FP format
#LEAST_NUM = "0.0"
format_dec_precision = "145" #This is hard-coded for precision 23
rho = mpfr('100')
#fassn=open("var-list.txt","r")#dummy file opened
#fassn=open("assignments/"+sys.argv[1].split("/")[2].rstrip(".fml")+"-check.asn","w")
if 0:
 input_file_name_split = sys.argv[1].split("/")
 fassn=open("assignments/"+sys.argv[1].split("/")[len(input_file_name_split) - 1].rstrip(".fml").rstrip(".smt2")+"-check.asn","w")
else:
 fassn=open("assignments/general.assn","w")
#fassn.close()
########### Data structures ############
RelOp = ['<','>','=','>=','<=']
def isRelOp(op):
  return(op in RelOp)

ArithOp = ['+','-','*','/']
def isArithOp(op):
  return(op in ArithOp)

PropOp = ['not','and','or']
def isPropOp(op):
  return(op in PropOp)

def myprint(s):
  #print(s)# for python3.4
  print(s) #for python 2.7

def get_op(op,op_type):
  if('R' == op_type):
    return op+"R"
  else:
    return op

def encode_into_mathsat_format(exp):
  num = ""
  num_dict = {}
  keys = []
  key = 0
  while(1):
    key = key+1
    num = re.search("\ [0-9]+.[0-9]+", exp)
    #num = re.search("\ [0-9]+.[0-9]+( |\))", exp)
    #print num.group()
      #print "Hi"
    if(num == None):
      break
    #symb=num.group()[:-1]
    #print symb
    num_dict["k"+str(key)]=num.group()
    exp = exp.replace(num.group()," k"+str(key))

  for item in num_dict.keys():
    print item
    exp = exp.replace(item,"((_ to_fp 8 24) RTZ "+num_dict[item]+")")

  exp = exp.replace("<=","fp.leq")
  exp = exp.replace(">=","fp.geq")
  exp = exp.replace("+","fp.add RNE ")
  p = re.compile(ur'-(?!\d)')
  #test_str = u"(- a -1024)\n\n"
  subst = u"fp.sub RNE"
  exp = re.sub(p, subst, exp)
  #exp = exp.replace("-","fp.sub RNE ")
  exp = exp.replace("*","fp.mul RNE ")
  exp = exp.replace("/","fp.div RNE ")
  exp = exp.replace(">","fp.gt")
  exp = exp.replace("<","fp.lt")
  exp = exp.replace("=","fp.eq")
  #following for handling negtive numbers, like -153.6495
  num2 = ""
  num_dict2 = {}
  keys2 = []
  key2 = 0
  while(1):
    key2 = key2+1
    num2 = re.search("\ -[0-9]+.[0-9]+", exp)
    #print num.group()
      #print "Hi"
    if(num2 == None):
      break
    num_dict2["k"+str(key2)]=num2.group()
    exp = exp.replace(num2.group()," k"+str(key2))

  for item in num_dict2.keys():
    with_minus = num_dict2[item]
    smtlib_const = "(- "+num_dict2[item][2:]+")"
    exp = exp.replace(item,"((_ to_fp 8 24) RTN "+smtlib_const+")")
  return exp

def get_smtlib_pneumonic(op):
 op_smtlib_pneumonic = {'+':'add','-':'sub','*':'mul','/':'div','<':'fp.lt','<=':'fp.leq','>':'fp.gt','>=':'fp.geq','=':'fp.eq'}
 return op_smtlib_pneumonic[op]

#My Exception class
class MyError:
  def __init__(self, value):
    self.value = value

  def __str__(self):
    return repr(self.value)

# Representation of an Arithmetic Variable
class Var:
  def __init__(self, gd, name):#, fp_val, real_val):
    # n is the number of variables excluded from the relaxed set,
    # i.e., |I| + |M|. Check : should it expect that here?
    self.left = None # not reqd.?
    self.right = None #not reqd.?
    #self.index = index #required?
    self.name = name #name of the variable, this is a string
    self.fp_val = mpfr('1')#fp_val
    self.fp_solver_val = mpfr('0')#check if this is mpfr with original prec
    set_fpa(gd.precision + 1, gd.exponent)
    #self.abstract_solver_val =
    if (gd.abstraction=="lfp"):
      self.abstract_solver_val = mpfr('0')#check if this is mpfr with reduced prec
      self.abstract_val = mpfr('1')# "CFR"
    else:
      self.abstract_solver_val = Fraction(0,1)
      self.abstract_val = Fraction(1,1)# "CFR"
    #self.abstract_val = mpfr('1')# "CFR"
    #for i in range(0,n):# ideally, n is |I| +|M|, which is known only within transform() after RedundantSet computation (simplify)
    set_context(ieee(32))
    self.support = {}
    self.contains_vars = [name]
    self.complexity = {name:1}
    self.name = name
    gd.ordered[self] = name

  #return degree of var in this variable
  def deg(self, var):
    if(self == var):
      return 1
    else:
      return 0

  def print_one_smtlib_stmt(self, gd):
    if(gd.abstraction == "real"):#(gd.generate_benchmark_real):
        smtlib_stmt = "(declare-fun "+ self.name + " () Real)"
    elif(gd.abstraction == "approx"):#(gd.generate_benchmark_dreal):
        smtlib_stmt = "(declare-fun "+ self.name + " () Real [-1000000000.0,1000000000.0])"
    else:#gd.abstraction = "lfp"
        smtlib_stmt = "(declare-fun "+ self.name + " () (_ FloatingPoint "+str(gd.exponent)+" "+str(gd.precision+1)+"))"
    if((not gd.abstraction == "real") and (not gd.abstraction == "approx") and (gd.enable_only_normal or gd.enable_only_normal_var) and (not gd.checking_phase)):#(not gd.generate_benchmark_real) and (not gd.generate_benchmark_dreal)
      smtlib_stmt += "\n(assert (fp.isNormal "+ self.name +"))"
    #following line added for testing assoc-example only, add one in ArithExp too
    #smtlib_stmt+="\n(assert (fp.gt " + self.name + " ((_ to_fp "+str(gd.exponent)+" "+str(gd.precision+1)+") RTN 0.0)))"
    #smtlib_stmt+="\n(assert (fp.lt " + self.name + " ((_ to_fp "+str(gd.exponent)+" "+str(gd.precision+1)+") RTN 1024.0)))"
    return smtlib_stmt

  def refine(self):
    return True

  def preorder(self):
    return self.name

  def occurs_in(self, var):
    return (self == var)

  def evaluate_update_fp(self,var):
   #print "Returning: "+str(self.fp_val)
   return self.fp_val

  def evaluate_update_fp_all(self):
   #print "Returning: "+str(self.fp_val)
   return self.fp_val

  def evaluate_update_prec_all(self):
   return self.abstract_val

  def evaluate_update_mixed_all(self):
   #print "Returning: "+str(self.fp_val)
   return self.abstract_val

  #def preorder_replace(self,var,name):
  # num = self.fp_val.as_integer_ratio()
  # num_as_smt2_string = "(/ "+str(num[0])+".0 "+str(num[1]) +".0)"
  # if (self == var):
  #  return "(+ "+str(num_as_smt2_string)+" "+name+")"
  # return str(num_as_smt2_string)
  def delta_one_smtlib(self, var):
    pre=""
    succ=""
    sign=""
    if (0 > self.fp_val):
     pre = "("
     succ = ")"
     sign = "- "
     val_str= "{0:.165Df}".format(self.fp_val)[1:]
    else:
     val_str= "{0:.165Df}".format(self.fp_val)
    #smtlib_stmt = "(define-fun "+ self.name + " () (_ FloatingPoint "+str(gd.exponent)+" "+str(gd.precision+1)+") ((_ to_fp "+ str(gd.exponent) +" "+ str(gd.precision+1)+") RTN "+pre+sign+val_str+"))"+succ
    if(self == var):#this the variable for which delta is added
      return "(fp.add RNE ((_ to_fp 8 24) RTN "+pre+sign+val_str+succ+") delta_"+self.name+")"
    else:
      return "((_ to_fp 8 24) RTN "+pre+sign+val_str+succ+")"

  def delta_vars_smtlib(self, vars):
    pre=""
    succ=""
    sign=""
    if (0 > self.fp_val):
     pre = "("
     succ = ")"
     sign = "- "
     val_str= "{0:.165Df}".format(self.fp_val)[1:]
    else:
     val_str= "{0:.165Df}".format(self.fp_val)
    #smtlib_stmt = "(define-fun "+ self.name + " () (_ FloatingPoint "+str(gd.exponent)+" "+str(gd.precision+1)+") ((_ to_fp "+ str(gd.exponent) +" "+ str(gd.precision+1)+") RTN "+pre+sign+val_str+"))"+succ
    if(self in vars):#this the variable for which delta is added
      return "(fp.add RNE ((_ to_fp 8 24) RTN "+pre+sign+val_str+succ+") delta_"+self.name+")"
    else:
      return "((_ to_fp 8 24) RTN "+pre+sign+val_str+succ+")"

  def delta_all_smtlib(self):
    pre=""
    succ=""
    sign=""
    if (0 > self.fp_val):
     pre = "("
     succ = ")"
     sign = "- "
     val_str= "{0:.165Df}".format(self.fp_val)[1:]
    else:
     val_str= "{0:.165Df}".format(self.fp_val)
    #smtlib_stmt = "(define-fun "+ self.name + " () (_ FloatingPoint "+str(gd.exponent)+" "+str(gd.precision+1)+") ((_ to_fp "+ str(gd.exponent) +" "+ str(gd.precision+1)+") RTN "+pre+sign+val_str+"))"+succ
    return "(fp.add RNE ((_ to_fp 8 24) RTN "+pre+sign+val_str+succ+") delta_"+self.name+")"


  def preorder_replace(self,var,name):
   #following 4 lines added for streamlining:
   if(self==var):
     return "(+ "+"{0:.165Df}".format(self.fp_val)+" "+name+")"
   else:
     return "{0:.165Df}".format(self.fp_val)
   #following lines commented for streamlining
   #num_as_smt2_string = "{0:.145Df}".format(self.fp_val)
   #if (self == var):
   # return "(+ "+str(num_as_smt2_string)+" "+name+")"
   #return str(num_as_smt2_string)

  def get_arith_vars(self):
   return [self]

  #returns False if there exists a supp support value that is negative
  def all_non_neg(self, supp):
   for k,v in self.support.iteritems():
    #print "all_non_neg(): Support of "+self.name+ " for "+k.name+" in direction "+direction(supp)+": "+str(v[supp])
    if v[supp] < 0:
     return False
   return True

  #find the total supp support value across all Invertible props
  #pre: assumes all v[supp] are non-negative
  def total_supp(self,supp):
   total_support = 0
   for k,v in self.support.iteritems():
    if('I'== k.type):
    	total_support +=v[supp]
   return total_support

  #returns True if there exists a supp support value that is positive
  #for some invertible proposition. It does NOT check if the support
  #value for other props is non-negative.
  def one_pos_invertible(self, supp):
   for k,v in self.support.iteritems():
     #print "one_pos_invertible(): Support of "+self.name+ " for "+k.name+" in direction "+direction(supp)+": "+str(v[supp])
     if(v[supp] > 0) and ('I' == k.type):
      return True
   return False

  def print2(self):
    #print "Var print2()"
    return self.name

  def named_prefix(self):
    #print "Var named_prefix()"
    return self.name

def calculate(left, op, right):
  ctx = get_context()
  ctx.precision = 24; ctx.emax = 128; ctx.emin = -148; ctx.subnormalize =  True #also change emax and emin
  set_context(ctx)
  result = mpfr('0')
  if(op == '+'):
    result  = left + right
  elif(op == '-'):
    result = left - right
  elif(op == '*'):
    result = left * right
  elif(op == '/'):
    result = left/right
  return result


# Representation of an Arithmetic Constant
class Const:#CFR
  def __init__(self, fp_val, real_val,gd,name):
    self.name = name
    self.left = None #not reqd.?
    self.right = None #not reqd.?
    #self.index = index #required?
    self.original_val = real_val
    set_context(ieee(32)) #Hardcoded for now
    self.fp_val = mpfr(real_val)#fp_val assumes ieee(32) as the context
    self.fp_solver_val = mpfr('0')#mpfr('0')#later needs to be updated with appropriate value acc abstraction
    set_fpa(gd.precision + 1, gd.exponent, RoundDown)
    #myprint("Context for constant inititalzation in __init__ for constant "+str(get_context()))
    #self.abstract_val = mpfr(real_val)#mpfr('0') #later needs to be updated with appropriate value acc abstraction #CFR

    if (gd.abstraction=="lfp"):
      self.abstract_solver_val = mpfr('0')#check if this is mpfr with reduced prec
      self.abstract_val = mpfr(real_val)# "CFR"
    else:
      self.abstract_solver_val = Fraction(1,1)
      self.abstract_val = real_val# "CFR"
      assert (isinstance(real_val, Fraction))
    #self.abstract_solver_val = mpfr('1')#mpfr('2')#later needs to be updated with appropriate value acc abstraction
    set_context(ieee(32)) #Hardcoded for now
    if(gd.abstraction == "lfp"):
      myprint("Constant constructor "+ self.name+" FP: "+"{0:.165Df}".format(self.fp_val)+ " vs Abstract: " +"{0:.165Df}".format(self.abstract_val))
    else:
      myprint("Constant constructor "+ self.name+" FP: "+"{0:.165Df}".format(self.fp_val)+ " vs Abstract: ")
      assert isinstance(self.abstract_val, Fraction)
      print self.abstract_val

    self.contains_vars = []
    self.complexity = {name:0}
    gd.ordered[self] = name
    gd.consts[name]=self

  #return degree of var in this Const
  def deg(self, var):
    return 0

  def delta_one_smtlib(self, var):
    pre=""
    succ=""
    sign=""
    if (0 > self.fp_val):
     pre = "("
     succ = ")"
     sign = "- "
     val_str= "{0:.165Df}".format(self.fp_val)[1:]
    else:
     val_str= "{0:.165Df}".format(self.fp_val)
    #smtlib_stmt = "(define-fun "+ self.name + " () (_ FloatingPoint "+str(gd.exponent)+" "+str(gd.precision+1)+") ((_ to_fp "+ str(gd.exponent) +" "+ str(gd.precision+1)+") RTN "+pre+sign+val_str+"))"+succ
    return "((_ to_fp 8 24) RTN "+pre+sign+val_str+succ+")"

  def delta_vars_smtlib(self, vars):
    pre=""
    succ=""
    sign=""
    if (0 > self.fp_val):
     pre = "("
     succ = ")"
     sign = "- "
     val_str= "{0:.165Df}".format(self.fp_val)[1:]
    else:
     val_str= "{0:.165Df}".format(self.fp_val)
    #smtlib_stmt = "(define-fun "+ self.name + " () (_ FloatingPoint "+str(gd.exponent)+" "+str(gd.precision+1)+") ((_ to_fp "+ str(gd.exponent) +" "+ str(gd.precision+1)+") RTN "+pre+sign+val_str+"))"+succ
    return "((_ to_fp 8 24) RTN "+pre+sign+val_str+succ+")"

  def delta_all_smtlib(self):
    pre=""
    succ=""
    sign=""
    if (0 > self.fp_val):
     pre = "("
     succ = ")"
     sign = "- "
     val_str= "{0:.165Df}".format(self.fp_val)[1:]
    else:
     val_str= "{0:.165Df}".format(self.fp_val)
    #smtlib_stmt = "(define-fun "+ self.name + " () (_ FloatingPoint "+str(gd.exponent)+" "+str(gd.precision+1)+") ((_ to_fp "+ str(gd.exponent) +" "+ str(gd.precision+1)+") RTN "+pre+sign+val_str+"))"+succ
    return "((_ to_fp 8 24) RTN "+pre+sign+val_str+succ+")"

  #(define-fun lower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN 0.01))
  def print_one_smtlib_stmt(self, gd):
    pre=""
    succ=""
    sign=""
    if (0 > self.fp_val):
     pre = "("
     succ = ")"
     sign = "- "
     val_str= "{0:.165Df}".format(self.fp_val)[1:]
    else:
     val_str= "{0:.165Df}".format(self.fp_val)
    if(gd.abstraction =="real" or gd.abstraction =="approx"):#(gd.generate_benchmark_real or gd.generate_benchmark_dreal):
      #smtlib_stmt = "(define-fun "+ self.name + " () Real "+pre+sign+val_str+")"+succ
      smtlib_stmt = "(declare-fun "+ self.name + " () Real)\n"
      smtlib_stmt += "(assert (= "+ self.name + " " + pre+sign+val_str+")"+succ+")"
    else:
      smtlib_stmt = "(define-fun "+ self.name + " () (_ FloatingPoint "+str(gd.exponent)+" "+str(gd.precision+1)+") ((_ to_fp "+ str(gd.exponent) +" "+ str(gd.precision+1)+") RTN "+pre+sign+val_str+"))"+succ
    return smtlib_stmt

  def refine(self):
    return True

  def preorder(self):
    return str(self.fp_val)

  def occurs_in(self, var):
    return (self == var)

  def evaluate_update_fp(self,var):
   #print "Returning: "+str(self.fp_val)
   return self.fp_val

  def evaluate_update_prec_all(self):
   #if(gd.abstraction == "real" or gd.abstraction == "approx"):
   #  assert isinstance(self.abstract_val, Fraction)
   #print "Returning: "+str(self.abstract_val)
   return self.abstract_val

  def evaluate_update_fp_all(self):
   #print "Returning: "+str(self.fp_val)
   return self.fp_val

  def evaluate_update_mixed_all(self):
   #print "Returning: "+str(self.abstract_val)
   return self.abstract_val

  #def preorder_replace(self,name,const):
   #num = self.fp_val.as_integer_ratio()
   #num_as_smt2_string = "(/ "+str(num[0])+".0 "+str(num[1]) +".0)"
   #return num_as_smt2_string

  def preorder_replace(self,name,const):
    #commented on 1 May 2016
    #return "{0:.165Df}".format(self.fp_val)
    return "{0:.165Df}".format(self.fp_val)
   #following two lines commented for streamlining constants
   #num_as_smt2_string = "{0:.145Df}".format(self.fp_val)
   #return num_as_smt2_string

  def get_arith_vars(self):
   return []

  def print2(self):
    #print "Const print2()"
    #return str(self.fp_val)
    return "{0:.30Df}".format(self.fp_val)#(self.abstract_val)# commented on May 9

  def named_prefix(self):
    #print "Const named_prefix()"
    #return str(self.fp_val)
    return "{0:.30Df}".format(self.fp_val)#(self.abstract_val)#commented on May 9

# Representation of Arithmetic expressions
class ArithExp:
  def __init__(self, left_exp, arith_op, right_exp, gd, name):
    self.left = left_exp
    self.right = right_exp
    self.op = arith_op
    self.op_type = 'R' # Can be 'R' for Real, 'M' for mixed, 'F' for float
    self.fp_val = mpfr('1')
    self.fp_solver_val = mpfr('0')#check if this is mpfr with original prec
    set_fpa(gd.precision + 1, gd.exponent)
    #self.abstract_solver_val = mpfr('0')#check if this is mpfr with reduced prec
    #self.abstract_val = mpfr('1')
    if (gd.abstraction=="lfp"):
      self.abstract_solver_val = mpfr('0')#check if this is mpfr with reduced prec
      self.abstract_val = mpfr('1')# "CFR"
    else:
      self.abstract_solver_val = Fraction(0,1)
      self.abstract_val = Fraction(1,1)# "CFR"

    set_context(ieee(32))
    left_vars = self.left.contains_vars
    right_vars = self.right.contains_vars
    self.contains_vars = uniq(left_vars + right_vars)
    self.complexity = {}
    self.name = name
    gd.ordered[self] = name
    #CR: check complexity metric on test examples: just for power
    for var in self.contains_vars:
      self.complexity[var] = 0
      left_complexity = 0
      right_complexity = 0
      if var in left_vars:
        if(isinstance(self.left,ArithExp)):
          left_complexity = self.left.complexity[var]
        elif(isinstance(self.left, Var)):
          if (self.left.name == var):
            left_complexity = 1
          else:
            left_complexity = 0
        else:#Const
            left_complexity = 0

      if var in right_vars:
        if(isinstance(self.right,ArithExp)):
          right_complexity = self.right.complexity[var]
        elif(isinstance(self.right, Var)):
          if (self.right.name == var):
           right_complexity = 1
          else:
            right_complexity = 0
        else:#Const
          right_complexity = 0

      if self.op in ['*']:
        self.complexity[var] = left_complexity + right_complexity
      else:#self.op = '+' or '-' or '/'
        self.complexity[var] = max(left_complexity, right_complexity)
    print "$$$:"
    print self.complexity

  def deg(self, var):
    #print "COMPLEXITY (ArithExp)"
    #print self.complexity
    #print var.name
    #print [self.complexity[var.name]]
    #exit(0)
    if (var.name in self.complexity):
      return self.complexity[var.name]
    else:
      return 0

  #get all Arithmetic expressions from the Proposition
  def get_all_arithexps(self):
    arithexps=[self]
    left_is_arithexp = isinstance(self.left,ArithExp)
    if(None != self.right):
     right_is_arithexp = isinstance(self.right,ArithExp)
    else:
     right_is_arithexp = False
    if left_is_arithexp:
      arithexps+=self.left.get_all_arithexps()
    if right_is_arithexp:
      arithexps+=self.right.get_all_arithexps()
    return uniq(arithexps)

  def delta_one_smtlib(self, var):
    return "(fp." +get_smtlib_pneumonic(self.op) + " RNE " + self.left.delta_one_smtlib(var)+ " "+ self.right.delta_one_smtlib(var) +")"

  def delta_vars_smtlib(self, vars):
    return "(fp." +get_smtlib_pneumonic(self.op) + " RNE " + self.left.delta_vars_smtlib(vars)+ " "+ self.right.delta_vars_smtlib(vars) +")"

  def delta_all_smtlib(self):
    return "(fp." +get_smtlib_pneumonic(self.op) + " RNE " + self.left.delta_all_smtlib()+ " "+ self.right.delta_all_smtlib() +")"

  def print_one_smtlib_stmt(self, gd):
    #myprint("Inside print_one_smtlib() of ArithExp")
    if(gd.abstraction == "approx"):#(gd.generate_benchmark_dreal):
      #exit(0)
      smtlib_stmt = "(declare-fun "+ self.name + " () Real)\n"
      smtlib_stmt += "(assert (= "+ self.name + " (" + self.op + " "+ self.left.name + " "+self.right.name + ")))"
    elif(gd.abstraction == "real"):#(gd.generate_benchmark_real):
      smtlib_stmt = "(define-fun "+ self.name + " () Real (" + self.op + " "+ self.left.name + " "+self.right.name + "))"
      if('/' == self.op):#forcing divisor to be non-zero; z3 bug: could otherwise return such absurd assignments
        smtlib_stmt+= "\n(assert (not (= " + self.right.name  + " 0)))"
    else:#gd.abstraction = "lfp"
      smtlib_stmt = "(define-fun "+ self.name + " () (_ FloatingPoint "+str(gd.exponent)+" "+str(gd.precision+1)+") (fp."+ get_smtlib_pneumonic(self.op) + " RNE " + self.left.name + " "+self.right.name + "))"
    if((not gd.abstraction == "real") and (not gd.abstraction == "approx") and(gd.enable_only_normal or gd.enable_only_normal_arithexp) and (not gd.checking_phase)):#(not gd.generate_benchmark_real) and (not gd.generate_benchmark_dreal)
      smtlib_stmt += "\n(assert (fp.isNormal "+ self.name +"))"
    return smtlib_stmt

  def preorder(self):
    op = get_op(self.op,self.op_type)
    return "("+op+" "+self.left.preorder()+ " "+self.right.preorder()+")"

  def occurs_in(self,var):
    return (self.left.occurs_in(var) or self.right.occurs_in(var))


  def evaluate_update_fp(self,var):
   if ((self.left==None)and(self.right==None)):
    myprint("Possible Error in evaluate_update_fp of ArithExp")
    return self.fp_val
   var_in_left = self.left.occurs_in(var)
   var_in_right = self.right.occurs_in(var)
   if(not(var_in_left or var_in_right)):
    return self.fp_val
   if var_in_left:
    left_val = self.left.evaluate_update_fp(var)
   else:
    left_val = self.left.fp_val
   if var_in_right:
    right_val = self.right.evaluate_update_fp(var)
   else:
    right_val = self.right.fp_val
   if self.op == '+':
     self.fp_val = left_val + right_val
   elif self.op == '-':
     self.fp_val = left_val - right_val
   elif self.op == '*':
     self.fp_val = left_val * right_val
   elif self.op == '/':
     self.fp_val = left_val / right_val
   else:
    myprint("Unknown operator")
    return mpfr('0')
   myprint("Inside ArithExp, now evaluates to "+ str(self.fp_val) +" in FP")
   return self.fp_val

  #in class ArithExp
  #Add evaluate_update_mixed_all()
  #Add evaluate_update_mixed()

  def evaluate_update_prec_all(self):
   if ((self.left==None)and(self.right==None)):
    myprint("Possible Error in evaluate_update_fp of ArithExp")
    return self.abstract_val

   left_val = self.left.evaluate_update_prec_all()
   right_val = self.right.evaluate_update_prec_all()
   if self.op == '+':
     self.abstract_val = left_val + right_val
   elif self.op == '-':
     self.abstract_val = left_val - right_val
   elif self.op == '*':
     self.abstract_val = left_val * right_val
   elif self.op == '/':
     print type(left_val)
     print type(right_val)
     print self.name
     print left_val
     print right_val
     self.abstract_val = left_val / right_val
   else:
    myprint("Unknown operator")
    exit(0)
    return mpfr('0')
   return self.abstract_val

  def evaluate_update_fp_all(self):
   if ((self.left==None)and(self.right==None)):
    myprint("Possible Error in evaluate_update_fp of ArithExp")
    return self.fp_val

   left_val = self.left.evaluate_update_fp_all()
   right_val = self.right.evaluate_update_fp_all()
   if self.op == '+':
     self.fp_val = left_val + right_val
   elif self.op == '-':
     self.fp_val = left_val - right_val
   elif self.op == '*':
     self.fp_val = left_val * right_val
   elif self.op == '/':
     self.fp_val = left_val / right_val
   else:
    myprint("Unknown operator")
    return mpfr('0')
   return self.fp_val

  def evaluate_update_mixed_all(self):
   if ((self.left==None)or(self.right==None)):
    myprint("Possible Error in evaluate_update_mixed_all of ArithExp")
    return self.abstract_val

   left_val = self.left.evaluate_update_mixed_all()
   right_val = self.right.evaluate_update_mixed_all()
   if self.op == '+':
     result = Fraction._add(left_val,right_val)
   elif self.op == '-':
     result = Fraction._sub(left_val,right_val)
   elif self.op == '*':
     result = Fraction._mul(left_val,right_val)
   elif self.op == '/':
     result = Fraction._div(left_val,right_val)
   else:
    myprint("Unknown operator")
    return Fraction('0')
   if 4 == DEBUG_LEVEL:
     myprint("result before any check:")
     myprint(result)
   if('R'== self.op_type):
     self.abstract_val = result
   else:# 'M' == self.op_type
     #print gmpy2.get_context()
     self.abstract_val = Fraction("{0:.145Df}".format(mpfr(result)))
   if 4 == DEBUG_LEVEL:
     myprint("Mixed value of "+self.print2()+" is, with op type "+self.op_type)
     myprint(self.abstract_val)
     myprint("Just for Info, the same value as Fraction: ")
     myprint(Fraction(str(self.abstract_val)))
     if('M'==self.op_type):
       myprint("Value before rounding:")
       myprint(result)
       myprint("After rounding:")
       myprint(self.abstract_val)
   return self.abstract_val

  def preorder_replace(self,name,const):
   #following lines added for streamlining/constant propagation
   left_occurrence = self.left.occurs_in(name)
   right_occurrence = self.right.occurs_in(name)
   if (not(left_occurrence) and not(right_occurrence)):
     return "{0:.165Df}".format(calculate(self.left.fp_val, self.op ,self.left.fp_val))#CHECK!!
   if(not(left_occurrence)):
     left = "{0:.165Df}".format(self.left.fp_val)
   else:
     left = self.left.preorder_replace(name,const)
   if(not(right_occurrence)):
     right = "{0:.165Df}".format(self.right.fp_val)
   else:
     right = self.right.preorder_replace(name,const)
   return "("+self.op+" "+left+" "+right+")"

  #unstable refine for lower precision FP removed
  #returns True ONLY if not a single operator could be refined
  def refine(self):
   #print "Inside Arithmetic refine"
    refined = False#defined to allow different refinement options
    if('R' == self.op_type):
     self.op_type = 'M'
     refined = True
     myprint(self.print2()+ " refined by refining "+self.op)
     return False #uncomment this if refinement is one operator per iteration
    if(not(isinstance(self.right,Var)) and (not(isinstance(self.right,Const)))):
     not_refined_right = self.right.refine()
     refined = refined or not not_refined_right
    if refined:#uncomment this line and the next if refinement is one operator per iteration
     return False#
    if(not(isinstance(self.left,Var)) and (not(isinstance(self.left,Const)))):
     not_refined_left = self.left.refine()
     refined = refined or not not_refined_left
    return (not refined)


  def print2(self):
    return self.print_infix()

  def get_arith_vars(self):
   return self.left.get_arith_vars()+self.right.get_arith_vars()

  def print_infix(self):
    ret = "("
    ret+= self.left.print2()
    ret+=" "+self.op+" "
    ret+=self.right.print2()
    ret+= ")"
    return ret

  def named_prefix(self):
    ret = "("
    ret+=self.op+" "
    ret+= self.left.named_prefix()+" "
    ret+=self.right.named_prefix()
    ret+= ")"
    return ret

#converts numbers 0,1 into appropriate string: pretty printing
def direction(num_code):
 if(0 == num_code):
  direction_string = "Upward"
 elif (1 == num_code):
  direction_string = "Downward"
 else:
  direction_string = "Error"
 return direction_string

def invert_rel_op(rel_op):
#why does n't this function invert other supported relational operators?
 if('<' == rel_op):
  return '>='
 elif ('>' == rel_op):
  return '<='
 elif ('=' == rel_op):
  return 'not (='
 #following condition stmts added on Nov 21, 2015: check why these had been omitted
 elif ('<=' == rel_op):
  return '>'
 elif ('>=' == rel_op):
  return '<'

# Representation of Relational Expressions
class RelExp:
  def __init__(self, left_exp, rel_op, right_exp):
    self.left = left_exp
    self.rel_op = rel_op
    self.right = right_exp # check if this needs to be dealt with specially
			  # as a const for canonical form

  def preorder(self):
    return "("+self.rel_op+" "+self.left.preorder()+" "+self.right.preorder()+")"

  def occurs_in(self, var):
    return self.left.occurs_in(var) or self.right.occurs_in(var)

  def get_arith_vars(self):
   if (not (isinstance(self.right,Const))):
    right_vars = self.right.get_arith_vars()
   else:
    right_vars = []

   return self.left.get_arith_vars()+right_vars

  def print2(self):
    ret = "("
    ret+= self.left.print2()
    ret+=" "+self.rel_op+" "
    ret+=self.right.print2()
    ret+=")"
    return ret

  def named_prefix(self):
    ret = "("
    ret+=self.rel_op+" "
    ret+=self.left.named_prefix()
    ret+=" "+self.right.named_prefix()
    ret+=")"
    return ret

  #assumes invertible
  def preorder_invert_replace(self,name,const,val):
    suffix = ""
    if(True == val):
      if ('='==self.rel_op):
        suffix = ")"
      rel_op = invert_rel_op(self.rel_op)
    else:
      rel_op = self.rel_op #no inversion required
    return "(" +rel_op+" "+self.left.preorder_replace(name,const)+" "+self.right.preorder_replace(name,const)+")"+suffix

  #assumes maintainable: should be combined with above function
  def preorder_maintain_replace(self,name,const,val):
    suffix = ""
    if(False == val):
      if ('=' == self.rel_op):
         suffix = ")"
      rel_op = invert_rel_op(self.rel_op)
    else:
      rel_op = self.rel_op #no inversion required
    return "(" +rel_op+" "+self.left.preorder_replace(name,const)+" "+self.right.preorder_replace(name,const)+")"+suffix#not general

# Representation of a proposition
class Prop:
  def __init__(self, name, rel_exp, gd):#, abstract_eval, fp_eval):
    self.name = name
    self.type = 'I' # 'I' for Invertible, 'M' for Maintainable, 'X' for currently unclassified
    self.rel_exp  = rel_exp
    #CR: only one of mixed or ideal should remain - rename
    self.abstract_eval = False#real_eval
    #self.i#deal_eval = True #The value that the proposition should evaluate to, to match the sat assignment from RIA solver.
    self.fp_eval = False#fp_eval
    self.fp_solver_eval = False
    self.abstract_solver_eval = False
    self.name = name
    gd.ordered[self] = name

  #consider ONLY invertibles
  def deg(self, var):
    if('I' == self.type):
      return max(self.rel_exp.left.deg(var), self.rel_exp.right.deg(var))
    else:
      return 0

  def delta_one_smtlib(self, var):
    return  "(" +get_smtlib_pneumonic(self.rel_exp.rel_op) + " " + self.rel_exp.left.delta_one_smtlib(var) + " " + self.rel_exp.right.delta_one_smtlib(var) + ")"
    #return var.name

  def delta_vars_smtlib(self, vars):
    return  "(" +get_smtlib_pneumonic(self.rel_exp.rel_op) + " " + self.rel_exp.left.delta_vars_smtlib(vars) + " " + self.rel_exp.right.delta_vars_smtlib(vars) + ")"

  def delta_all_smtlib(self):
    return  "(" +get_smtlib_pneumonic(self.rel_exp.rel_op) + " " + self.rel_exp.left.delta_all_smtlib() + " " + self.rel_exp.right.delta_all_smtlib() + ")"

  #get all Arithmetic expressions from the Proposition
  def get_all_arithexps(self):
    arithexps=[]
    if isinstance(self.rel_exp.left,ArithExp):
      arithexps += self.rel_exp.left.get_all_arithexps()
    if(None != self.rel_exp.right):#is this check needed?
      if isinstance(self.rel_exp.right,ArithExp):
        arithexps += self.rel_exp.right.get_all_arithexps()
    return uniq(arithexps)

  def print_one_smtlib_stmt(self, gd):
    if(gd.abstraction == "approx"):#(gd.generate_benchmark_dreal):
      smtlib_stmt = "(declare-fun "+ self.name + " () Bool)\n"
      smtlib_stmt += "(assert (= "+ self.name + " (" + self.rel_exp.rel_op + " " + self.rel_exp.left.name + " " + self.rel_exp.right.name + ")))"
    elif(gd.abstraction == "real"):#(gd.generate_benchmark_real):
      smtlib_stmt = "(define-fun "+ self.name + " () Bool (" + self.rel_exp.rel_op + " " + self.rel_exp.left.name + " " + self.rel_exp.right.name + "))"
    else:#gd.abstraction = "lfp"
      smtlib_stmt = "(define-fun "+ self.name + " () Bool (" +get_smtlib_pneumonic(self.rel_exp.rel_op) + " " + self.rel_exp.left.name + " " + self.rel_exp.right.name + "))"
#) (fp."+ get_smtlib_pneumonic(self.op) + " RNE " + self.left.name + " "+self.right.name + "))"
    return smtlib_stmt

  def print_prop(self):
    myprint(self.name +":: FP (as str): "+str(self.fp_eval)+" Abstract (as str): "+str(self.abstract_eval))

  def invertibles(self):
    invertibles = []
    if('I' == self.type):
      invertibles+=[self]
    return invertibles

  def maintainables(self):
    maintainables = []
    if('M' == self.type):
      maintainables+=[self]
    return maintainables

  #refine
  def refine(self):
    #return (self.rel_exp.right.refine() and self.rel_exp.left.refine())
    failed = self.rel_exp.right.refine()
    if(not failed):
      return False
    failed = self.rel_exp.left.refine()
    return failed

  #assumes prop is invertible
  #def swap_if_necessary(self):
  def preorder(self):
    return self.rel_exp.preorder()

  def occurs_in(self, var):
    return (self.rel_exp.left.occurs_in(var) or self.rel_exp.right.occurs_in(var))

  def evaluate_fp_update_all(self):
   #print "Inside "+self.name+" evaluate_fp_update() for "+self.name
   left_val = self.rel_exp.left.evaluate_update_fp_all()
   	#print "returned from left call"

   right_val = self.rel_exp.right.evaluate_update_fp_all()
   	#print "returned from right call"

   if('<' == self.rel_exp.rel_op):
    self.fp_eval = (left_val < right_val)
   elif('>' == self.rel_exp.rel_op):
    self.fp_eval = (left_val > right_val)
   elif('<=' == self.rel_exp.rel_op):
    self.fp_eval = (left_val <= right_val)
   elif('>=' == self.rel_exp.rel_op):
    self.fp_eval = (left_val >= right_val)
   elif('=' == self.rel_exp.rel_op):
    self.fp_eval = (left_val == right_val)
   #print "returning fp_eval: "+str(self.fp_eval)
   #The following lines only make sense if real values have already been updated
   #if((self.fp_eval == self.abstract_eval) and self.type == 'I'):
   # self.type = 'M'
    #print "Confirmation: proposition "+self.name+" is now Maintainable"
   #elif((self.fp_eval != self.abstract_eval) and self.type == 'M'):
   # self.type = 'I'
    #print "ERROR: Proposition "+self.name +" changed from Maintainable to Invertible!"
   return self.fp_eval

  def evaluate_real_update_all(self):
   #print "Inside "+self.name+" evaluate_fp_update() for "+self.name
   left_val = self.rel_exp.left.evaluate_update_real_all()#removed Fraction(str from around rvalue
   right_val = self.rel_exp.right.evaluate_update_real_all()#same comment as above

   if('<' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val < right_val)
   elif('>' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val > right_val)
   elif('<=' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val <= right_val)
   elif('>=' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val >= right_val)
   elif('=' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val == right_val)
   else:
    myprint("Unhandled relational operator: "+self.rel_exp.rel_op)
   #print "returning fp_eval: "+str(self.fp_eval)
   #The following lines only make sense if FP values have already been updated
   #if(self.abstract_eval == self.fp_eval):# and self.type == 'I'):
   # self.type = 'M'
    #print "Confirmation: proposition "+self.name+" is now Maintainable"
   #elif(self.abstract_eval != self.fp_eval):# and self.type == 'M'):
   # self.type = 'I'
    #print "ERROR: Proposition "+self.name +" changed from Maintainable to Invertible!"
   return self.abstract_eval

  def evaluate_prec_update_all(self):
   #print "Inside "+self.name+" evaluate_fp_update() for "+self.name
   left_val = self.rel_exp.left.evaluate_update_prec_all()
        #print "returned from left call"

   right_val = self.rel_exp.right.evaluate_update_prec_all()
        #print "returned from right call"

   #check
   if('<' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val < right_val)
   elif('>' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val > right_val)
   elif('<=' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val <= right_val)
   elif('>=' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val >= right_val)
   elif('=' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val == right_val)
   else:
    myprint("Unhandled relational operator: "+self.rel_exp.rel_op)
   #print "returning abstract_eval: "+str(self.mixed_eval)
   #The following lines only make sense if real values have already been updated
   #if((self.fp_eval == self.abstract_eval) and self.type == 'I'):
   # self.type = 'M'
    #print "Confirmation: proposition "+self.name+" is now Maintainable"
   #elif((self.fp_eval != self.abstract_eval) and self.type == 'M'):
   # self.type = 'I'
    #print "ERROR: Proposition "+self.name +" changed from Maintainable to Invertible!"
   return self.abstract_eval

  def evaluate_mixed_update_all(self):
   #print "Inside "+self.name+" evaluate_fp_update() for "+self.name
   left_val = self.rel_exp.left.evaluate_update_mixed_all()
        #print "returned from left call"

   right_val = self.rel_exp.right.evaluate_update_mixed_all()
        #print "returned from right call"
   #check
   if('<' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val < right_val)
   elif('>' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val > right_val)
   elif('<=' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val <= right_val)
   elif('>=' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val >= right_val)
   elif('=' == self.rel_exp.rel_op):
    self.abstract_eval = (left_val == right_val)
   else:
    myprint("Unhandled relational operator: "+self.rel_exp.rel_op)
   #print "returning abstract_eval: "+str(self.mixed_eval)
   #The following lines only make sense if real values have already been updated
   #if((self.fp_eval == self.abstract_eval) and self.type == 'I'):
   # self.type = 'M'
    #print "Confirmation: proposition "+self.name+" is now Maintainable"
   #elif((self.fp_eval != self.abstract_eval) and self.type == 'M'):
   # self.type = 'I'
    #print "ERROR: Proposition "+self.name +" changed from Maintainable to Invertible!"
   return self.abstract_eval

  def evaluate_fp_update(self,var):
   myprint("Inside class Prop evaluate_fp_update() for "+self.name)
   var_in_left = self.rel_exp.left.occurs_in(var)
   var_in_right = self.rel_exp.right.occurs_in(var)
   if(not(var_in_left or var_in_right)):
   	return self.fp_eval
   if(var_in_left):
   	left_val = self.rel_exp.left.evaluate_update_fp(var)
   	#print "returned from left call"
   else:
   	left_val = self.rel_exp.left.fp_val
   if(var_in_right):
   	right_val = self.rel_exp.right.evaluate_update_fp(var)
   	#print "returned from right call"
   else:
   	right_val = self.rel_exp.right.fp_val

   if('<' == self.rel_exp.rel_op):
    self.fp_eval = (left_val < right_val)
   elif('>' == self.rel_exp.rel_op):
    self.fp_eval = (left_val > right_val)
   elif('<=' == self.rel_exp.rel_op):
    self.fp_eval = (left_val <= right_val)
   elif('>=' == self.rel_exp.rel_op):
    self.fp_eval = (left_val >= right_val)
   elif('==' == self.rel_exp.rel_op):
    self.fp_eval = (left_val == right_val)
   #print "returning fp_eval: "+str(self.fp_eval)
   #The following lines only make sense if real values have already been updated
   #if((self.fp_eval == self.abstract_eval) and self.type == 'I'):
   # self.type = 'M'
   # print "Confirmation: proposition "+self.name+" is now Maintainable"
   #elif((self.fp_eval != self.abstract_eval) and self.type == 'M'):
   # self.type = 'I'
   # print "ERROR: Proposition "+self.name +" changed from Maintainable to Invertible!"
   myprint(self.name+ " now evaluates to "+str(self.fp_eval) +" in FP")
   return self.fp_eval

  def get_all_props(self):
    return self

  #assumes self is an invertible prop
  def preorder_invert_replace(self,name,const):
   prop_string = self.rel_exp.preorder_invert_replace(name,const,self.fp_eval)
   return prop_string

  def preorder_maintain_replace(self,name,const):
   prop_string = self.rel_exp.preorder_maintain_replace(name,const,self.fp_eval)
   return prop_string

  def categorize_prop(self):
   if (self.abstract_eval == self.fp_eval):
    # abstract and fp values are the same, so Maintainable
    self.type = 'M'
   else:
    self.type = 'I'

  def invertible_prop(self):
   return ('I' == self.type)

  def get_arith_vars(self):
   return self.rel_exp.get_arith_vars()

  def print2(self):
    ret = ""
    #the following is if the relational expression needs to be printed
    ret= "("+self.name+":: "+self.rel_exp.print2()+")"
    #ret = self.name
    return ret

  def named_prefix(self):
    ret = ""
    #the following is if the relational expression needs to be printed
    ret= "(: "+self.name + " " + self.rel_exp.named_prefix()+")"
    #ret = self.name
    return ret

# Representation of Propositional Expressions
class PropExp:
  def __init__(self, gd, name, left_exp, bool_op, right_exp):#, real_eval, fp_eval):
    self.left_exp = left_exp
    self.bool_op = bool_op
    self.right_exp = right_exp # 'None' for the unary boolean operator not
    #CR: only one of mixed or ideal: and rename
    #self.i#deal_eval = True#the value that real arith solver assigns to this exp when SAT
    self.abstract_eval = True
    self.fp_eval = False
    self.fp_solver_eval = False
    self.abstract_solver_eval = False
    self.name = name
    gd.ordered[self] = name

  #counts the degree of var in invertibles ONLY!
  def deg(self, var):
   #deg_inv_list = []
   #for i in self.invertibles():
   if(None!= self.right_exp):
     return max(self.left_exp.deg(var),self.right_exp.deg(var))
   else:
     return self.left_exp.deg(var)

  def print_one_smtlib_stmt(self, gd):
    if('not'==self.bool_op):
      right_part = ""
    else:
      right_part = " "+ self.right_exp.name
    if(gd.abstraction == "approx"):#(gd.generate_benchmark_dreal):
      smtlib_stmt = "(declare-fun "+ self.name + " () Bool)\n"
      smtlib_stmt += "(assert (= "+ self.name + " (" + self.bool_op + " " + self.left_exp.name + right_part + ")))"
    else:
      smtlib_stmt = "(define-fun "+ self.name + " () Bool (" +self.bool_op + " " + self.left_exp.name + right_part + "))"
#) (fp."+ get_smtlib_pneumonic(self.op) + " RNE " + self.left.name + " "+self.right.name + "))"
    return smtlib_stmt

  def occurs_in(self, var):
    if None!= self.right_exp:
      return (self.left_exp.occurs_in(var) or self.right_exp.occurs_in(var))
    else:
      return self.left_exp.occurs_in(var)

  def print_all_props(self):
    for p in self.get_all_props():
      myprint(p.name +":: FP: "+str(p.fp_eval)+" Abstract: "+str(p.abstract_eval))

  def evaluate_fp_update(self,var):
   myprint("Inside PropExp evaluate_fp_update()")
   var_in_left = self.left_exp.occurs_in(var)
   if(None!=self.right_exp):
     var_in_right = self.right_exp.occurs_in(var)
   else:
     var_in_right = False
   if(not (var_in_left or var_in_right)):
    return self.fp_eval
   if var_in_left:
     left_val = self.left_exp.evaluate_fp_update(var)
   	#print "returned from left call"
   else:
     left_val = self.left_exp.fp_eval
   if((None != self.right_exp) and var_in_right):
     right_val = self.right_exp.evaluate_fp_update(var)
    	#print "returned from right call"
   else:
     if (None!=self.right_exp):
       right_val = self.right_exp.fp_eval

   if('or' == self.bool_op):
    self.fp_eval = (left_val or right_val)
   elif('and' == self.bool_op):
    self.fp_eval = (left_val and right_val)
   if('not' == self.bool_op):
    self.fp_eval = (not left_val)
   #print "returning fp_eval: "+str(self.fp_eval)
   myprint("PropExp() instance, now evaluates to "+str(self.fp_eval))
   return self.fp_eval

  def evaluate_fp_update_all(self):
   print "Inside PropExp evaluate_fp_update_all()"
   left_val = self.left_exp.evaluate_fp_update_all()
   if(None!=self.right_exp):#this can happen if self.bool_op is a 'not
     right_val = self.right_exp.evaluate_fp_update_all()
   if('or' == self.bool_op):
     self.fp_eval = (left_val or right_val)
   elif('and' == self.bool_op):
     self.fp_eval = (left_val and right_val)
   if('not' == self.bool_op):
     self.fp_eval = (not left_val)
   #print "returning fp_eval: "+str(self.fp_eval)
   return self.fp_eval

  def evaluate_prec_update_all(self):
    #print "Inside PropExp evaluate_mixed_update_all()"
    left_val = self.left_exp.evaluate_prec_update_all()
    if(None!=self.right_exp):#this can happen if self.bool_op is a 'not
      right_val = self.right_exp.evaluate_prec_update_all()
    if('or' == self.bool_op):
      self.abstract_eval = (left_val or right_val)
    elif('and' == self.bool_op):
      self.abstract_eval = (left_val and right_val)
    if('not' == self.bool_op):
      self.abstract_eval = (not left_val)
    #print "returning fp_eval: "+str(self.abstract_eval)
    return self.abstract_eval


  def evaluate_mixed_update_all(self):
    #print "Inside PropExp evaluate_mixed_update_all()"
    left_val = self.left_exp.evaluate_mixed_update_all()
    if(None!=self.right_exp):#this can happen if self.bool_op is a 'not
      right_val = self.right_exp.evaluate_mixed_update_all()
    if('or' == self.bool_op):
      self.abstract_eval = (left_val or right_val)
    elif('and' == self.bool_op):
      self.abstract_eval = (left_val and right_val)
    if('not' == self.bool_op):
      self.abstract_eval = (not left_val)
    #print "returning fp_eval: "+str(self.abstract_eval)
    return self.abstract_eval

  #get all propositions from a Propositional expression
  def get_all_props(self):
    props=[]
    #following one required?: should never occur
    if isinstance(self.left_exp,Prop):
      #print "left is a prop: "+self.left_exp.name
      props+=[self.left_exp]
    else:
      props+=self.left_exp.get_all_props()
    if(None != self.right_exp):
     if isinstance(self.right_exp,Prop):
       #print "right is a prop: "+self.right_exp.name
       props+=[self.right_exp]
     else:
       props+=self.right_exp.get_all_props()
    return uniq(props)


  #get all Arithmetic expressions from a Propositional expression
  def get_all_arithexps(self):
    arithexps=[]
    arithexps += self.left_exp.get_all_arithexps()
    if(None != self.right_exp):
      arithexps += self.right_exp.get_all_arithexps()
    return uniq(arithexps)

  def generate_smtlib_fp(self,gd):
   #def generate_smtlib(gd):
 #  lis = string(gd.ordered())
 #  for lit in :
 #    if(isinstance(lit,PropExp)):
 #      print str(lit)+'='+str(lit.left_exp)+' '+str(lit.bool_op)+' '+str(lit.right_exp)
 #    else:
 #      print "Skipping "+str(lit)
   #reverse of written parse
   return ""

  #this procedure writes into the type field of all propositions in it
  def categorize_props(self):
   if isinstance(self.left_exp,Prop):
    self.left_exp.categorize_prop()
   else:
    self.left_exp.categorize_props()
   if isinstance(self.right_exp,Prop):
    self.right_exp.categorize_prop()
   else:
     if None!=self.right_exp:
      self.right_exp.categorize_props()

  def print2(self):
    ret="("
    if self.bool_op=='not':
      ret+="not "+self.left_exp.print2()
    else:
      ret+=self.left_exp.print2()
      ret+=" "+self.bool_op
      ret+=" "+self.right_exp.print2()
    ret+=")"
    return ret

  def named_prefix(self):
    ret="("
    if self.bool_op=='not':
      ret+="not "+self.left_exp.named_prefix()
    else:
      ret+=self.bool_op
      ret+=" "+self.left_exp.named_prefix()
      ret+=" "+self.right_exp.named_prefix()
    ret+=")"
    return ret

  def invertibles(self):
   invertibles = []
   if isinstance(self.left_exp,Prop):
    if('I' == self.left_exp.type):
     invertibles+=[self.left_exp]
   else:
     invertibles+=self.left_exp.invertibles()
   if isinstance(self.right_exp,Prop):
    if('I' == self.right_exp.type):
     invertibles+=[self.right_exp]
   else:
    if(None!=self.right_exp):
      invertibles+=self.right_exp.invertibles()
   return uniq(invertibles)

  def maintainables(self):
   maintainables = []
   if isinstance(self.left_exp,Prop):
    if('M' == self.left_exp.type):
     maintainables+=[self.left_exp]
   else:
     maintainables+=self.left_exp.maintainables()
   if isinstance(self.right_exp,Prop):
    if('M' == self.right_exp.type):
     maintainables+=[self.right_exp]
   else:
    if(None!=self.right_exp):
      maintainables+=self.right_exp.maintainables()
   return uniq(maintainables)

  def get_arith_vars(self):
   right_var_list = []
   if None != self.right_exp:
    right_var_list = self.right_exp.get_arith_vars()
   return uniq(self.left_exp.get_arith_vars()+right_var_list)

  def dependency_table(self,ctx):
   #CR: rho should be global!
   rho = mpfr('100')#might not be essential
   #get all arith variables
   arith_vars = uniq(self.get_arith_vars())
   #get all invertible variables
   invertibles = uniq(self.invertibles())
   #get all maintainable variables
   maintainables = uniq(self.maintainables())
   #print invertibles+maintainables
   #for every arith variable, do the following
   for var in arith_vars:
    #construct a dictionary support with the prop object as key and the upward /downward support as the value
     #for every prop in I \cup M
     # compute the upward/downward support value delta_us and delta_ds
     #look up the table to assign the upward/downward support value
    for prop in invertibles+maintainables:
     print "Dep: "+prop.name
     print prop.rel_exp.rel_op
     #continue
     if (not (var in prop.get_arith_vars())):
      var.support[prop] = [mpfr('0'),mpfr('0')]
      break
     delta_us = get_delta_us(var,prop,ctx)
     delta_ds = get_delta_ds(var,prop,ctx)
     if('I'==prop.type):#Support for Invertible Props
      if(('>'==prop.rel_exp.rel_op)or('>='==prop.rel_exp.rel_op)):
       if(False==prop.fp_eval):#to be changed to True
        var.support[prop]= [delta_us,delta_ds]
       else:#True==prop.fp_eval
        var.support[prop]= [-delta_us,-delta_ds]
      elif(('<'==prop.rel_exp.rel_op)or('<='==prop.rel_exp.rel_op)):
       print "Applied to "+p.name+" "+var.name
       if(False==prop.fp_eval):#to be changed to True
        var.support[prop]= [-delta_us,-delta_ds]
       else:#True==prop.fp_eval
        var.support[prop]= [delta_us,delta_ds]
      elif('='==prop.rel_exp.rel_op):
       if(prop.rel_exp.left.fp_val < prop.rel_exp.right.fp_val):#an increase in LHS value expected to make it equal to RHS
        var.support[prop]= [delta_us, delta_ds]
       else:#a decrease in LHS value expected to make it equal to RHS
        var.support[prop]= [-delta_us,-delta_ds]

     elif('M'==prop.type):#Support for Maintainable Props
      #var.support[prop]=[10000,1]
      if(('>'==prop.rel_exp.rel_op)or('>='==prop.rel_exp.rel_op)):
       if(True==prop.fp_eval):#to be maintained True
        var.support[prop]= [delta_us,delta_ds]
       else:#False==prop.fp_eval
        var.support[prop]= [-delta_us,-delta_ds]
      elif(('<'==prop.rel_exp.rel_op)or('<='==prop.rel_exp.rel_op)):
       if(True==prop.fp_eval):#to be maintained True
        var.support[prop]= [-delta_us,-delta_ds]
       else:#False==prop.fp_eval
        var.support[prop]= [delta_us,delta_ds]
      elif('='==prop.rel_exp.rel_op):#This should be retained as such
        #var.support[prop]= [-abs(delta_us)*rho,-abs(delta_ds)*rho]#check: abs should be gmpy2's abs
        var.support[prop]= [-mpfr('1.0'*rho),-mpfr('-1.0')*rho]#replacement for above line on May 4, 2016
     #elif('M'==prop.type):
      #var.support[prop]=[10000,1]
     #var.support[prop]=[delta_us,1.0]#This should be decided on the basis of the table:w

     #print var.support[prop]
   return

  def preorder(self):
    if('not'==self.bool_op):
      return "(not "+ self.left_exp.preorder()+")"
    else:
      return "("+self.bool_op+ " "+self.left_exp.preorder()+ " "+self.right_exp.preorder()+")"
#selects the next variable to be changed, along with the proposition in which
# it is to be attempted
#return value: (<var-name>,<direction>,<the value of support in that direction for that variable>,
#<name of the selected proposition>)
  def next_var(self):
   max_dir  = 0
   max_var = None
   maximum = 0 #to be changed for the zero issue?
   for var in self.get_arith_vars():
    total_support = [0,0]
    local_max = 0
    local_max_dir = None
    for supp in [0,1]:
     if(var.all_non_neg(supp) and var.one_pos_invertible(supp)):
      total_support[supp] = var.total_supp(supp)

    if(total_support[0] >= total_support[1]):
     local_max = total_support[0]
     local_max_dir = 0
    else:
     local_max = total_support[1]
     local_max_dir = 1

    if local_max >= maximum:
     maximum = local_max
     max_var = var
     max_dir = local_max_dir

   #compute and return the proposition to be Inverted
   max_support = 0
   selected_prop = None
   # This is for a given "var" and a given direction of support "supp"
   # Pre: every support is non-negative and atleast one pos supp for a prop in dir supp
   if(None != max_var):
     for k,v in max_var.support.iteritems():
      if ('I' == k.type) and (v[max_dir] >= max_support):
       max_support = v[supp]
       selected_prop = k

     if(None == selected_prop):
      myprint("No var./prop could be selected for delta-change")
      return (None,0,0,None)
   #return max_prop
     myprint("Results from next_var: Var selected ="+max_var.name+", Direction = "+direction(max_dir)+", Proposition to be changed = "+selected_prop.name)
   return (max_var,max_dir,maximum,selected_prop)

  def value_change1(self, gd, all_arith_vars):
   all_props = []
   for p in  self.get_all_props():
     all_props += [p]
   delta_constraint = ""
   for var in all_arith_vars:
     delta_constraint+="(declare-fun delta_"+var.name+" () (_ FloatingPoint 8 24))\n"
     bound = var.fp_val*mpfr(gd.bound)#delta for a variable being restricted to 1% of the value for that variable

   if(gd.enable_delta_bounds):
     if(var.fp_val > 0):
       delta_constraint+="(assert (and (fp.gt delta_"+var.name+" ((_ to_fp 8 24) RTN (- "+"{0:.165Df}".format(bound)+")))(fp.lt delta_"+var.name+" ((_ to_fp 8 24) RTN "+"{0:.165Df}".format(bound)+"))))\n"
     else:
       delta_constraint+="(assert (and (fp.lt delta_"+var.name+" ((_ to_fp 8 24) RTN "+"{0:.165Df}".format(mpfr('-1.0')*bound)+"))(fp.gt delta_"+var.name+" ((_ to_fp 8 24) RTN (- "+"{0:.165Df}".format(mpfr('-1.0')*bound)+")))))\n"

   for p in all_props:
     delta_constraint += "(define-fun "+p.name+" () Bool "+p.delta_all_smtlib()+")\n"

   #CHECK: not being handled here
   before0=""; after0=""; before1=""; after1=""
   if(False ==  all_props[0].abstract_eval):
     before0 = "(not "; after0 = ")"
   if(False ==  all_props[1].abstract_eval):
     before1 = "(not "; after1 = ")"
   delta_constraint+="(define-fun propexp-delta0"+ " () Bool (and "+before0+all_props[0].name+after0+" "+before1+all_props[1].name+after1+"))\n"
   for i in range(1, len(all_props)-1):
     before=""; after="";
     if(False ==  all_props[i+1].abstract_eval):
       before = "(not "; after = ")"
     delta_constraint+="(define-fun propexp-delta"+str(i)+ " () Bool (and propexp-delta"+str(i-1)+" "+before+all_props[i+1].name+after+"))\n"
   delta_constraint+="(assert propexp-delta"+str(len(all_props)-2)+")\n(check-sat)\n(exit)"
   print delta_constraint
   #exit(0)
   if "MATHSAT" == D_SOLVER:
     #final_str = "(declare-fun delta () (_ FloatingPoint 8 24)); ADDED\n(define-fun lower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv8388608 32))); CHANGED: lowest ~ 2^-126\n(define-fun nlower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv2155872256 32))); CHANGED: nlowest ~ NEG 2^-126\n(define-fun nhigher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv3296722944 32))); CHANGED: NEG 1024.0\n(define-fun higher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1149239296 32))); CHANGED: 1024.0\n(define-fun c1 () Bool (or (and (fp.lt delta higher) (fp.lt lower delta)) (and (fp.lt delta nlower) (fp.lt nhigher delta))))\n(assert c1)\n"
     #final_str = "(declare-fun delta () (_ FloatingPoint 8 24)); ADDED\n;(define-fun     lower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv8388608 32))); CHANGED: lowest ~ 2^-126\n;(define-fun nlower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv2155872256 32))); CHANGED: nlowest ~ NEG 2^-126\n;(define-fun nhigher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv3296722944 32))); CHANGED: NEG 1024.0\n;(define-fun higher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1149239296 32))); CHANGED: 1024.0\n;(define-fun c1 () Bool (or   (and (fp.lt delta higher) (fp.lt lower delta)) (and (fp.lt delta nlower) (fp.lt nhigher  delta))))\n;(assert c1)\n"
     #if(gd.enable_only_normal_delta):
     #  final_str+="(assert (fp.isNormal delta))\n"
     #if (0 == direction):
     #  final_str+="(assert (fp.gt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
     #else:
     #  final_str+="(assert (fp.lt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
     #final_str+="(define-fun skeleton () Bool " + encode_into_mathsat_format(constraint)+")\n"
     #final_str+="(assert skeleton)\n(check-sat)\n(exit)"
     input_file_name_split = gd.input_filename.split("/")
     delta_filename="smt2_files/"+input_file_name_split[len(input_file_name_split) - 1].rstrip(".fml").rstrip(".smt2")+"_iter_"+str(gd.iteration)+"_delta.smt2"
     f1=open(delta_filename,"w")
     f1.write(delta_constraint)
     f1.close()
     #if(0 != direction):
     # print "Aborting"
     # exit(1)
       #print final_str
   else:# "REALIZER" == D_SOLVER
   # START OF REALIZER ENCODING COMMENTED OUT
   ## call and get back Realizer encoding (just the translator, don't call z3 as yet) of constraint1 and \not constraint2
     ps = subprocess.Popen(('echo', constraint), stdout=subprocess.PIPE)
   #global TRANSLATOR_CFG_FP
     TRANSLATOR_CFG_FP="examples/single-prec-modified2.cfg"
     myprint("I'm using for delta constraint this file: "+TRANSLATOR_CFG_FP)
     output = subprocess.check_output((TRANSLATOR_PATH,TRANSLATOR_CFG_FP,'var-list.txt'), stdin=ps.stdout)#USE appropriate CONFIG file acc to PRECISION/RANGE
     ps.wait()
     myprint("Translator-expts o/p: "+output)
     output = output.replace("(check-sat)\n(get-model)","")
     if (0==direction):#attempting to increase the variable; delta should be positive
      output+="(assert (fp.gt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
    #two lines below commented out for elimintaing min-delta
    #output+="(assert (=> (>= (- delta (/ 1.0  two-to-exp-p-minus-e-delta)) "+LEAST_NUM+") (= pred-delta (- delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
    #output+="(assert (=> (< (- delta (/ 1.0  two-to-exp-p-minus-e-delta)) "+LEAST_NUM+") (= pred-delta 0.0)))\n"
     else:#attempting to decrease the variable; delta should be negative
      output+="(assert (fp.lt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
    #below two lines commented out for eliminating min-delta
    #output+="(assert (=> (<= (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)) (- "+LEAST_NUM+")) (= pred-delta (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
    #output+="(assert (=> (> (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)) (- "+LEAST_NUM+")) (= pred-delta 0.0)))\n"

   #output+="(assert (=> (> delta 0.0) (= pred-delta (- delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
   #output+="(assert (=> (< delta 0.0) (= pred-delta (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)))))"
     output+="\n(check-sat)\n(get-model)"
     f1=open("z3-delta-constraint.smt2","w")
     f1.write(output)
     f1.close()
   #END OF REALIZER ENCODING COMMENTED OUT
   #print "Start: "+output
   #ps2 = subprocess.Popen(('echo', output), stdout=subprocess.PIPE)
   #ps2.wait()
   if "MATHSAT" == D_SOLVER:
     try:
      myprint("Calling mathsat on small formula to get delta: ")
      ferror=open("debug.smt2","w")
      ferror.write(delta_constraint)
      ferror.close()
      myprint(ctime())
      t1=time()
      #ps2 = subprocess.Popen(('cat', 'mathsat-delta-constraint.smt2'), stdout=subprocess.PIPE)
      #ps2.wait()
      #output2 = subprocess.check_output(('mathsat','-theory.fp.mode=0','-theory.eq_propagation=false','-printer.fp_number_format=0','-model'),stdin=ps2.stdout,stderr=subprocess.STDOUT)
      if(True):#('Linux'==platform.system()):
       output2 = subprocess.check_output(('timeout',gd.inner_timeout,'mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=0','-theory.fp.bit_blast_mode=1' ,'-model',delta_filename), stderr=subprocess.STDOUT)
       myprint("delta_filename: "+delta_filename)
       myprint("Mathsat output:\n"+output2)
      #exit(1)
      else:
       output2 = subprocess.check_output(('mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=0','-theory.fp.bit_blast_mode=1' ,'-model', delta_filename), stderr=subprocess.STDOUT)
       myprint("Mathsat output:\n"+output2)
      if ("unsat"==output2[0:5]):
        t2=time()
        fstat.write("%.2fsN\t" % (t2 - t1))
        myprint(ctime())
        myprint(output2)
        msg="UNSATISFIABLE delta constraint for "+gd.input_filename+" during iteration "+str(gd.iteration)
        myprint(msg)
        fdbg=open(gd.molly_debug_file,"a")
        fdbg.write(msg+"\n")
        fdbg.close()
        return {}#mpfr('0')#Fraction(0,1)
      t2=time()
      fstat.write("%.2fs\t" % (t2 - t1))
      print(ctime())
      #exit(1)
      #NOTE: selection policy will be 1 here; if-then-else redundant!
      if(0 == gd.var_selection_policy):
        delta_list = parse_mathsat_output(output2,['delta'],"unsigned_int",gd)
      elif(1 == gd.var_selection_policy):
        list_to_read_back = []

        for var in self.get_arith_vars():
          list_to_read_back += ['delta_'+var.name]
        delta_list = parse_mathsat_output(output2,list_to_read_back,"unsigned_int",gd)
      elif(2 == gd.var_selection_policy):
        myprint("Not yet implemented\n");exit(1)
      else:
        myprint("Not yet implemented\n");exit(1)
      print "delta_list"
      print delta_list
      delta_assn = {} #This is the delta assignment dictionary to be returned
      if(None==delta_list or "error"==delta_list):
        delta = mpfr('0')#Fraction(0,1)
        myprint("Mathsat for delta: UNKNOWN")
        t2=time()
        fstat.write("%.2fsU\t" % (t2 - t1))
      else:
        for delta_var in delta_list.keys():
          delta = delta_list[delta_var]
          myprint("delta (unsigned int) = "+delta)
          ps3 = subprocess.Popen(('echo', delta), stdout=subprocess.PIPE)
          output3 = subprocess.check_output(('scripts/to_decimal'), stdin=ps3.stdout)#USE appropriate CONFIG file acc to PRECISION/RANGE
          ps3.wait()
          myprint(output3)
        #delta = "{0:.165Df}".format(output3)
        #delta = Fraction(output3)#mpfr(Fraction(output3))?: Oct 14
          delta = mpfr(mpq(output3))
          myprint(delta_var+": ")
          print delta
          delta_assn[delta_var] = delta
        #myprint("delta (decimal): ")
        #myprint(delta)
        #exit(1)
     except subprocess.CalledProcessError:
      delta = mpfr('0')#Fraction(0,1)
      delta_assn = {}
      myprint("Mathsat for delta: UNKNOWN")
      t2=time()
      fstat.write("%.2fsU\t" % (t2 - t1))
     except MyError as e:
      myprint(e)
      delta = mpfr('0')#Fraction(0,1)
      delta_assn = {}
      t2=time()
      fstat.write("%.2fsE\t" % (t2 - t1))
      #exit(0)
     fstat.flush()
     os.fsync(fstat)
     return delta_assn

   else:#z3 is the solver: PARSING NOT CHANGED FOR MULTIPLE DELTA VARS: WILL NOT WORK NOW
     try:
      myprint("Calling z3 on small formula to get delta: ")
      ferror=open("debug.smt2","w")
      ferror.write(output)
      ferror.close()
      myprint(ctime())
      t1=time()
      output2 = subprocess.check_output(('z3','-st','-smt2','-T:'+str(Z3_DELTA_TIMEOUT),'z3-delta-constraint.smt2'),stderr=subprocess.STDOUT)
      t2=time()
      fstat.write("%.2fs\t" % (t2 - t1))
      myprint(ctime())
    #print output2
      delta_list = parse_solver_output(output2,['delta'])
      myprint("delta_list")
      myprint(delta_list)
      delta = delta_list['delta']
      myprint("DELTA: ")
      myprint(delta)
     except subprocess.CalledProcessError:
      delta = Fraction(0,1)
      myprint("z3 for delta: UNKNOWN")
      t2=time()
      fstat.write("%.2fsU\t" % (t2 - t1))
     except MyError as e:
      myprint(e)
      delta = Fraction(0,1)
      t2=time()
      fstat.write("%.2fsO\t" % (t2 - t1))
      #exit(0)
     fstat.flush()
     os.fsync(fstat)
     return delta

  def value_change2(self, gd, var, number_vars, timeout):
   all_props = []
   for p in  self.get_all_props():
     all_props += [p]
   delta_constraint = ""
   delta_constraint+="(declare-fun delta_"+var.name+" () (_ FloatingPoint 8 24))\n"
   bound = var.fp_val*mpfr(gd.bound)#delta for a variable being restricted to a percentage of the current value assigned to that variable
   if(gd.enable_delta_bounds):
     if(var.fp_val > 0):
       delta_constraint+="(assert (and (fp.gt delta_"+var.name+" ((_ to_fp 8 24) RTN (- "+"{0:.165Df}".format(bound)+")))(fp.lt delta_"+var.name+" ((_ to_fp 8 24) RTN "+"{0:.165Df}".format(bound)+"))))\n"
     else:
       delta_constraint+="(assert (and (fp.lt delta_"+var.name+" ((_ to_fp 8 24) RTN "+"{0:.165Df}".format(mpfr('-1.0')*bound)+"))(fp.gt delta_"+var.name+" ((_ to_fp 8 24) RTN (- "+"{0:.165Df}".format(mpfr('-1.0')*bound)+")))))\n"

   for p in all_props:
     delta_constraint += "(define-fun "+p.name+" () Bool "+p.delta_one_smtlib(var)+")\n"

   #CHECK: not being handled here
   before0=""; after0=""; before1=""; after1=""
   if(False ==  all_props[0].abstract_eval):
     before0 = "(not "; after0 = ")"
   if(False ==  all_props[1].abstract_eval):
     before1 = "(not "; after1 = ")"
   # ASSUMING input FPA formula is of a particular form when using "approx":
   # A Conjunction, so all props HAVE TO BE TRUE
   # Otherwise:  technically incorrect!!
   if(gd.abstraction == "approx"):
     before0 = before1 = after0 = after1 = ""
   delta_constraint+="(define-fun propexp-delta0"+ " () Bool (and "+before0+all_props[0].name+after0+" "+before1+all_props[1].name+after1+"))\n"
   for i in range(1, len(all_props)-1):
     before=""; after="";
     if(False ==  all_props[i+1].abstract_eval):
       before = "(not "; after = ")"

     # ASSUMING input FPA formula is of a particular form when using "approx":
     # A Conjunction, so all props HAVE TO BE TRUE
     # Otherwise:  technically incorrect!!
     if(gd.abstraction == "approx"):
       before = after = ""
     delta_constraint+="(define-fun propexp-delta"+str(i)+ " () Bool (and propexp-delta"+str(i-1)+" "+before+all_props[i+1].name+after+"))\n"
   delta_constraint+="(assert propexp-delta"+str(len(all_props)-2)+")\n(check-sat)\n(exit)"
   print delta_constraint
   #exit(0)
   if "MATHSAT" == D_SOLVER:
     #final_str = "(declare-fun delta () (_ FloatingPoint 8 24)); ADDED\n(define-fun lower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv8388608 32))); CHANGED: lowest ~ 2^-126\n(define-fun nlower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv2155872256 32))); CHANGED: nlowest ~ NEG 2^-126\n(define-fun nhigher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv3296722944 32))); CHANGED: NEG 1024.0\n(define-fun higher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1149239296 32))); CHANGED: 1024.0\n(define-fun c1 () Bool (or (and (fp.lt delta higher) (fp.lt lower delta)) (and (fp.lt delta nlower) (fp.lt nhigher delta))))\n(assert c1)\n"
     #final_str = "(declare-fun delta () (_ FloatingPoint 8 24)); ADDED\n;(define-fun     lower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv8388608 32))); CHANGED: lowest ~ 2^-126\n;(define-fun nlower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv2155872256 32))); CHANGED: nlowest ~ NEG 2^-126\n;(define-fun nhigher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv3296722944 32))); CHANGED: NEG 1024.0\n;(define-fun higher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1149239296 32))); CHANGED: 1024.0\n;(define-fun c1 () Bool (or   (and (fp.lt delta higher) (fp.lt lower delta)) (and (fp.lt delta nlower) (fp.lt nhigher  delta))))\n;(assert c1)\n"
     #if(gd.enable_only_normal_delta):
     #  final_str+="(assert (fp.isNormal delta))\n"
     #if (0 == direction):
     #  final_str+="(assert (fp.gt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
     #else:
     #  final_str+="(assert (fp.lt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
     #final_str+="(define-fun skeleton () Bool " + encode_into_mathsat_format(constraint)+")\n"
     #final_str+="(assert skeleton)\n(check-sat)\n(exit)"
     input_file_name_split = gd.input_filename.split("/")
     delta_filename="smt2_files/"+input_file_name_split[len(input_file_name_split) - 1].rstrip(".fml").rstrip(".smt2")+"_iter_"+str(gd.iteration)+"_delta.smt2"
     f1=open(delta_filename,"w")
     f1.write(delta_constraint)
     f1.close()
     #if(0 != direction):
     # print "Aborting"
     # exit(1)
       #print final_str
   else:# "REALIZER" == D_SOLVER
   # START OF REALIZER ENCODING COMMENTED OUT
   ## call and get back Realizer encoding (just the translator, don't call z3 as yet) of constraint1 and \not constraint2
     ps = subprocess.Popen(('echo', constraint), stdout=subprocess.PIPE)
   #global TRANSLATOR_CFG_FP
     TRANSLATOR_CFG_FP="examples/single-prec-modified2.cfg"
     myprint("I'm using for delta constraint this file: "+TRANSLATOR_CFG_FP)
     output = subprocess.check_output((TRANSLATOR_PATH,TRANSLATOR_CFG_FP,'var-list.txt'), stdin=ps.stdout)#USE appropriate CONFIG file acc to PRECISION/RANGE
     ps.wait()
     myprint("Translator-expts o/p: "+output)
     output = output.replace("(check-sat)\n(get-model)","")
     if (0==direction):#attempting to increase the variable; delta should be positive
      output+="(assert (fp.gt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
    #two lines below commented out for elimintaing min-delta
    #output+="(assert (=> (>= (- delta (/ 1.0  two-to-exp-p-minus-e-delta)) "+LEAST_NUM+") (= pred-delta (- delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
    #output+="(assert (=> (< (- delta (/ 1.0  two-to-exp-p-minus-e-delta)) "+LEAST_NUM+") (= pred-delta 0.0)))\n"
     else:#attempting to decrease the variable; delta should be negative
      output+="(assert (fp.lt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
    #below two lines commented out for eliminating min-delta
    #output+="(assert (=> (<= (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)) (- "+LEAST_NUM+")) (= pred-delta (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
    #output+="(assert (=> (> (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)) (- "+LEAST_NUM+")) (= pred-delta 0.0)))\n"

   #output+="(assert (=> (> delta 0.0) (= pred-delta (- delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
   #output+="(assert (=> (< delta 0.0) (= pred-delta (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)))))"
     output+="\n(check-sat)\n(get-model)"
     f1=open("z3-delta-constraint.smt2","w")
     f1.write(output)
     f1.close()
   #END OF REALIZER ENCODING COMMENTED OUT
   #print "Start: "+output
   #ps2 = subprocess.Popen(('echo', output), stdout=subprocess.PIPE)
   #ps2.wait()
   if "MATHSAT" == D_SOLVER:
     try:
      myprint("Calling mathsat on small formula to get delta: ")
      ferror=open("debug.smt2","w")
      ferror.write(delta_constraint)
      ferror.close()
      if(gd.select_all_vars_in_sequence):
        single_inner_timeout = max(float(gd.inner_timeout)/float(number_vars), gd.tmin_lift)
      else:
        single_inner_timeout = gd.inner_timeout
      myprint(ctime())
      t1=time()
      #ps2 = subprocess.Popen(('cat', 'mathsat-delta-constraint.smt2'), stdout=subprocess.PIPE)
      #ps2.wait()
      #output2 = subprocess.check_output(('mathsat','-theory.fp.mode=0','-theory.eq_propagation=false','-printer.fp_number_format=0','-model'),stdin=ps2.stdout,stderr=subprocess.STDOUT)
      #timeout = str(float(gd.inner_timeout)/float(number_vars))#fixed value of 60 used in FMCAD16 submission
      force_lower_to = False
      #to_str = ""
      if(True):#('Linux'==platform.system()):
       time_left = float(gd.overall_timeout) - float(t1 - gd.start_time)
       if time_left < 0:
        myprint("Overall timeout exceeded before inner loop in iteration "+str(gd.iteration))
        print_final(gd)#TODO:enhance to stats printing
       if(time_left < float(single_inner_timeout)):
        to = str(time_left)
        force_lower_to = True
        #to_str = "T"
       else:
        to = single_inner_timeout
       output2 = subprocess.check_output(('timeout',to,'mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=0','-theory.fp.bit_blast_mode=1' ,'-model',delta_filename), stderr=subprocess.STDOUT)
       myprint("delta_filename: "+delta_filename)
       myprint("Mathsat output:\n"+output2)
      #exit(1)
      else:
       output2 = subprocess.check_output(('mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=0','-theory.fp.bit_blast_mode=1' ,'-model', delta_filename), stderr=subprocess.STDOUT)
       myprint("Mathsat output:\n"+output2)
      if ("unsat"==output2[0:5]):
        t2=time()
        fstat.write("%.2fsN\t" % (t2 - t1))
        myprint(ctime())
        myprint(output2)
        msg="UNSATISFIABLE delta constraint for "+gd.input_filename+" during iteration "+str(gd.iteration)
        myprint(msg)
        fdbg=open(gd.molly_debug_file,"a")
        fdbg.write(msg+"\n")
        fdbg.close()
        return {}#mpfr('0')#Fraction(0,1)
      t2=time()
      fstat.write("%.2fs\t" % (t2 - t1))
      print(ctime())
      #exit(1)
      #NOTE: gd.var_selection_policy is 2 here!!
      if(0 == gd.var_selection_policy):
        delta_list = parse_mathsat_output(output2,['delta'],"unsigned_int",gd)
      elif(1 == gd.var_selection_policy):
        list_to_read_back = []
        for var in self.get_arith_vars():
          list_to_read_back += ['delta_'+var.name]
        delta_list = parse_mathsat_output(output2,list_to_read_back,"unsigned_int",gd)
      elif((2 == gd.var_selection_policy) or (4 == gd.var_selection_policy)):
        list_to_read_back = ['delta_'+var.name]
        delta_list = parse_mathsat_output(output2,list_to_read_back,"unsigned_int",gd)
      else:
        myprint("Not yet implemented\n");exit(1)
      print "delta_list"
      print delta_list
      delta_assn = {} #This is the delta assignment dictionary to be returned
      if(None==delta_list or "error"==delta_list):
        delta = mpfr('0')#Fraction(0,1)
        myprint("Mathsat for delta: UNKNOWN")
        t2=time()
        fstat.write("%.2fsU\t" % (t2 - t1))
      else:
        for delta_var in delta_list.keys():
          delta = delta_list[delta_var]
          myprint("delta (unsigned int) = "+delta)
          ps3 = subprocess.Popen(('echo', delta), stdout=subprocess.PIPE)
          output3 = subprocess.check_output(('scripts/to_decimal'), stdin=ps3.stdout)#USE appropriate CONFIG file acc to PRECISION/RANGE
          ps3.wait()
          myprint(output3)
        #delta = "{0:.165Df}".format(output3)
        #delta = Fraction(output3)#mpfr(Fraction(output3))?: Oct 14
          delta = mpfr(mpq(output3))
          myprint(delta_var+": ")
          print delta
          delta_assn[delta_var] = delta
        #myprint("delta (decimal): ")
        #myprint(delta)
        #exit(1)
     except subprocess.CalledProcessError:
      t2=time()
      if(force_lower_to):
       fstat.write("%.2fsT\t" % float(to))
       print_final(gd)
      else:
       fstat.write("%.2fst\t" % (t2 - t1))

      delta = mpfr('0')#Fraction(0,1)
      delta_assn = {}

     except MyError as e:
      myprint(e)
      delta = mpfr('0')#Fraction(0,1)
      delta_assn = {}
      t2=time()
      fstat.write("%.2fsE\t" % (t2 - t1))
      #exit(0)
     fstat.flush()
     os.fsync(fstat)
     return delta_assn

   else:#z3 is the solver: PARSING NOT CHANGED FOR MULTIPLE DELTA VARS: WILL NOT WORK NOW
     try:
      myprint("Calling z3 on small formula to get delta: ")
      ferror=open("debug.smt2","w")
      ferror.write(output)
      ferror.close()
      myprint(ctime())
      t1=time()
      output2 = subprocess.check_output(('z3','-st','-smt2','-T:'+str(Z3_DELTA_TIMEOUT),'z3-delta-constraint.smt2'),stderr=subprocess.STDOUT)
      t2=time()
      fstat.write("%.2fs\t" % (t2 - t1))
      myprint(ctime())
    #print output2
      delta_list = parse_solver_output(output2,['delta'])
      myprint("delta_list")
      myprint(delta_list)
      delta = delta_list['delta']
      myprint("DELTA: ")
      myprint(delta)
     except subprocess.CalledProcessError:
      delta = Fraction(0,1)
      myprint("z3 for delta: UNKNOWN")
      t2=time()
      fstat.write("%.2fsU\t" % (t2 - t1))
     except MyError as e:
      myprint(e)
      delta = Fraction(0,1)
      t2=time()
      fstat.write("%.2fsO\t" % (t2 - t1))
      #exit(0)
     fstat.flush()
     os.fsync(fstat)
     return delta

  def value_change0(self,var,direction,prop,gd):
   #only changing
   #prop_new = prop.preorder_invert_replace()
   #the following line added for streamlining/constant propagation
   prop.evaluate_fp_update_all()
   constraint1 =  prop.preorder_invert_replace(var,"delta")#fix take into account T/F and op
   myprint("constraint1: ")
   myprint(constraint1)
   #constraint2 = prop.preorder_invert_replace(var,"pred-delta")
   #constraint2 = invert_rel_expr_str(constraint2)
   #print "constraint2: "
   #print constraint2
   constraint = constraint1 #commented out for eliminating pred-delta "(and " + constraint1 + constraint2 + ")"
   for prop_m in self.maintainables():
     #myprint(prop_m.get_arith_vars())
     if(var in prop_m.get_arith_vars()):
       constraint = "(and "+ constraint + prop_m.preorder_maintain_replace(var,"delta") + ")"
   myprint("delta constraint: "+ constraint)
   #START OF MATHSAT CONSTRAINT
   if "MATHSAT" == D_SOLVER:
     #final_str = "(declare-fun delta () (_ FloatingPoint 8 24)); ADDED\n(define-fun lower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv8388608 32))); CHANGED: lowest ~ 2^-126\n(define-fun nlower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv2155872256 32))); CHANGED: nlowest ~ NEG 2^-126\n(define-fun nhigher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv3296722944 32))); CHANGED: NEG 1024.0\n(define-fun higher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1149239296 32))); CHANGED: 1024.0\n(define-fun c1 () Bool (or (and (fp.lt delta higher) (fp.lt lower delta)) (and (fp.lt delta nlower) (fp.lt nhigher delta))))\n(assert c1)\n"
     final_str = "(declare-fun delta () (_ FloatingPoint 8 24)); ADDED\n;(define-fun     lower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv8388608 32))); CHANGED: lowest ~ 2^-126\n;(define-fun nlower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv2155872256 32))); CHANGED: nlowest ~ NEG 2^-126\n;(define-fun nhigher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv3296722944 32))); CHANGED: NEG 1024.0\n;(define-fun higher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1149239296 32))); CHANGED: 1024.0\n;(define-fun c1 () Bool (or   (and (fp.lt delta higher) (fp.lt lower delta)) (and (fp.lt delta nlower) (fp.lt nhigher  delta))))\n;(assert c1)\n"
     #if(gd.enable_only_normal_delta):
     #  final_str+="(assert (fp.isNormal delta))\n"
     #if (0 == direction):
     #  final_str+="(assert (fp.gt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
     #else:
     #  final_str+="(assert (fp.lt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
     final_str+="(define-fun skeleton () Bool " + encode_into_mathsat_format(constraint)+")\n"
     final_str+="(assert skeleton)\n(check-sat)\n(exit)"
     input_file_name_split = gd.input_filename.split("/")
     delta_filename="smt2_files/"+input_file_name_split[len(input_file_name_split) - 1].rstrip(".fml").rstrip(".smt2")+"_iter_"+str(gd.iteration)+"_delta.smt2"
     f1=open(delta_filename,"w")
     f1.write(final_str)
     f1.close()
     #if(0 != direction):
     # print "Aborting"
     # exit(1)
       #print final_str
   else:# "REALIZER" == D_SOLVER
   # START OF REALIZER ENCODING COMMENTED OUT
   ## call and get back Realizer encoding (just the translator, don't call z3 as yet) of constraint1 and \not constraint2
     ps = subprocess.Popen(('echo', constraint), stdout=subprocess.PIPE)
   #global TRANSLATOR_CFG_FP
     TRANSLATOR_CFG_FP="examples/single-prec-modified2.cfg"
     myprint("I'm using for delta constraint this file: "+TRANSLATOR_CFG_FP)
     output = subprocess.check_output((TRANSLATOR_PATH,TRANSLATOR_CFG_FP,'var-list.txt'), stdin=ps.stdout)#USE appropriate CONFIG file acc to PRECISION/RANGE
     ps.wait()
     myprint("Translator-expts o/p: "+output)
     output = output.replace("(check-sat)\n(get-model)","")
     if (0==direction):#attempting to increase the variable; delta should be positive
      output+="(assert (fp.gt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
    #two lines below commented out for elimintaing min-delta
    #output+="(assert (=> (>= (- delta (/ 1.0  two-to-exp-p-minus-e-delta)) "+LEAST_NUM+") (= pred-delta (- delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
    #output+="(assert (=> (< (- delta (/ 1.0  two-to-exp-p-minus-e-delta)) "+LEAST_NUM+") (= pred-delta 0.0)))\n"
     else:#attempting to decrease the variable; delta should be negative
      output+="(assert (fp.lt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
    #below two lines commented out for eliminating min-delta
    #output+="(assert (=> (<= (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)) (- "+LEAST_NUM+")) (= pred-delta (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
    #output+="(assert (=> (> (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)) (- "+LEAST_NUM+")) (= pred-delta 0.0)))\n"

   #output+="(assert (=> (> delta 0.0) (= pred-delta (- delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
   #output+="(assert (=> (< delta 0.0) (= pred-delta (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)))))"
     output+="\n(check-sat)\n(get-model)"
     f1=open("z3-delta-constraint.smt2","w")
     f1.write(output)
     f1.close()
   #END OF REALIZER ENCODING COMMENTED OUT
   #print "Start: "+output
   #ps2 = subprocess.Popen(('echo', output), stdout=subprocess.PIPE)
   #ps2.wait()
   if "MATHSAT" == D_SOLVER:
     try:
      myprint("Calling mathsat on small formula to get delta: ")
      ferror=open("debug.smt2","w")
      ferror.write(final_str)
      ferror.close()
      myprint(ctime())
      t1=time()
      #ps2 = subprocess.Popen(('cat', 'mathsat-delta-constraint.smt2'), stdout=subprocess.PIPE)
      #ps2.wait()
      #output2 = subprocess.check_output(('mathsat','-theory.fp.mode=0','-theory.eq_propagation=false','-printer.fp_number_format=0','-model'),stdin=ps2.stdout,stderr=subprocess.STDOUT)
      if(True):#('Linux'==platform.system()):
       output2 = subprocess.check_output(('timeout',gd.inner_timeout,'mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=0','-theory.fp.bit_blast_mode=1' ,'-model',delta_filename), stderr=subprocess.STDOUT)
       myprint("delta_filename: "+delta_filename)
       myprint("Mathsat output:\n"+output2)
      #exit(1)
      else:
       output2 = subprocess.check_output(('mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=0','-theory.fp.bit_blast_mode=1' ,'-model', delta_filename), stderr=subprocess.STDOUT)
       myprint("Mathsat output:\n"+output2)
      if ("unsat"==output2[0:5]):
        t2=time()
        fstat.write("%.2fsN\t" % (t2 - t1))
        myprint(ctime())
        myprint(output2)
        msg="UNSATISFIABLE delta constraint for "+gd.input_filename+" during iteration "+str(gd.iteration)
        myprint(msg)
        fdbg=open(gd.molly_debug_file,"a")
        fdbg.write(msg+"\n")
        fdbg.close()
        return mpfr('0')#Fraction(0,1)
      t2=time()
      fstat.write("%.2fs\t" % (t2 - t1))
      print(ctime())
      #exit(1)
      delta_list = parse_mathsat_output(output2,['delta'],"unsigned_int",gd)
      #print "delta_list"
      #print delta_list
      if(None==delta_list or "error"==delta_list):
        delta = mpfr('0')#Fraction(0,1)
        myprint("Mathsat for delta: UNKNOWN")
        t2=time()
        fstat.write("%.2fsU\t" % (t2 - t1))
      else:
        delta = delta_list['delta']
        myprint("delta (unsigned int) = "+delta)
        ps3 = subprocess.Popen(('echo', delta), stdout=subprocess.PIPE)
        output3 = subprocess.check_output(('scripts/to_decimal'), stdin=ps3.stdout)#USE appropriate CONFIG file acc to PRECISION/RANGE
        ps3.wait()
        myprint(output3)
        #delta = "{0:.165Df}".format(output3)
        #delta = Fraction(output3)#mpfr(Fraction(output3))?: Oct 14
        delta = mpfr(mpq(output3))
        print delta
        #myprint("delta (decimal): ")
        #myprint(delta)
        #exit(1)
     except subprocess.CalledProcessError:
      delta = mpfr('0')#Fraction(0,1)
      myprint("Mathsat for delta: UNKNOWN")
      t2=time()
      fstat.write("%.2fsU\t" % (t2 - t1))
     except MyError as e:
      myprint(e)
      delta = mpfr('0')#Fraction(0,1)
      t2=time()
      fstat.write("%.2fsE\t" % (t2 - t1))
      #exit(0)
     fstat.flush()
     os.fsync(fstat)
     return delta

   else:
     try:
      myprint("Calling z3 on small formula to get delta: ")
      ferror=open("debug.smt2","w")
      ferror.write(output)
      ferror.close()
      myprint(ctime())
      t1=time()
      output2 = subprocess.check_output(('z3','-st','-smt2','-T:'+str(Z3_DELTA_TIMEOUT),'z3-delta-constraint.smt2'),stderr=subprocess.STDOUT)
      t2=time()
      fstat.write("%.2fs\t" % (t2 - t1))
      myprint(ctime())
    #print output2
      delta_list = parse_solver_output(output2,['delta'])
      myprint("delta_list")
      myprint(delta_list)
      delta = delta_list['delta']
      myprint("DELTA: ")
      myprint(delta)
     except subprocess.CalledProcessError:
      delta = Fraction(0,1)
      myprint("z3 for delta: UNKNOWN")
      t2=time()
      fstat.write("%.2fsU\t" % (t2 - t1))
     except MyError as e:
      myprint(e)
      delta = Fraction(0,1)
      t2=time()
      fstat.write("%.2fsO\t" % (t2 - t1))
      #exit(0)
     fstat.flush()
     os.fsync(fstat)
     return delta

  def value_change5(self, gd, inv_arith_vars, m_vars):
   all_props = []
   for p in  self.get_all_props():
     all_props += [p]
   delta_constraint = ""
   for var in m_vars:
     delta_constraint+="(declare-fun delta_"+var.name+" () (_ FloatingPoint 8 24))\n"
   for var in inv_arith_vars:
     delta_constraint+="(declare-fun delta_"+var.name+" () (_ FloatingPoint 8 24))\n"
     bound = var.fp_val*mpfr(gd.bound)#delta for a variable being restricted to 1% of the value for that variable

     if(gd.enable_delta_bounds):
       if(var.fp_val > 0):
         delta_constraint+="(assert (and (fp.gt delta_"+var.name+" ((_ to_fp 8 24) RTN (- "+"{0:.165Df}".format(bound)+")))(fp.lt delta_"+var.name+" ((_ to_fp 8 24) RTN "+"{0:.165Df}".format(bound)+"))))\n"
       else:
         delta_constraint+="(assert (and (fp.lt delta_"+var.name+" ((_ to_fp 8 24) RTN "+"{0:.165Df}".format(mpfr('-1.0')*bound)+"))(fp.gt delta_"+var.name+" ((_ to_fp 8 24) RTN (- "+"{0:.165Df}".format(mpfr('-1.0')*bound)+")))))\n"

   for p in all_props:
     delta_constraint += "(define-fun "+p.name+" () Bool "+p.delta_vars_smtlib(inv_arith_vars)+")\n"

   #CHECK: not being handled here
   before0=""; after0=""; before1=""; after1=""
   if(False ==  all_props[0].abstract_eval):
     before0 = "(not "; after0 = ")"
   if(False ==  all_props[1].abstract_eval):
     before1 = "(not "; after1 = ")"
   delta_constraint+="(define-fun propexp-delta0"+ " () Bool (and "+before0+all_props[0].name+after0+" "+before1+all_props[1].name+after1+"))\n"
   for i in range(1, len(all_props)-1):
     before=""; after="";
     if(False ==  all_props[i+1].abstract_eval):
       before = "(not "; after = ")"
     delta_constraint+="(define-fun propexp-delta"+str(i)+ " () Bool (and propexp-delta"+str(i-1)+" "+before+all_props[i+1].name+after+"))\n"
   delta_constraint+="(assert propexp-delta"+str(len(all_props)-2)+")\n(check-sat)\n(exit)"
   #print delta_constraint
   #exit(0)
   if "MATHSAT" == D_SOLVER:
     #final_str = "(declare-fun delta () (_ FloatingPoint 8 24)); ADDED\n(define-fun lower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv8388608 32))); CHANGED: lowest ~ 2^-126\n(define-fun nlower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv2155872256 32))); CHANGED: nlowest ~ NEG 2^-126\n(define-fun nhigher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv3296722944 32))); CHANGED: NEG 1024.0\n(define-fun higher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1149239296 32))); CHANGED: 1024.0\n(define-fun c1 () Bool (or (and (fp.lt delta higher) (fp.lt lower delta)) (and (fp.lt delta nlower) (fp.lt nhigher delta))))\n(assert c1)\n"
     #final_str = "(declare-fun delta () (_ FloatingPoint 8 24)); ADDED\n;(define-fun     lower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv8388608 32))); CHANGED: lowest ~ 2^-126\n;(define-fun nlower () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv2155872256 32))); CHANGED: nlowest ~ NEG 2^-126\n;(define-fun nhigher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv3296722944 32))); CHANGED: NEG 1024.0\n;(define-fun higher () (_ FloatingPoint 8 24) ((_ to_fp 8 24) (_ bv1149239296 32))); CHANGED: 1024.0\n;(define-fun c1 () Bool (or   (and (fp.lt delta higher) (fp.lt lower delta)) (and (fp.lt delta nlower) (fp.lt nhigher  delta))))\n;(assert c1)\n"
     #if(gd.enable_only_normal_delta):
     #  final_str+="(assert (fp.isNormal delta))\n"
     #if (0 == direction):
     #  final_str+="(assert (fp.gt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
     #else:
     #  final_str+="(assert (fp.lt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
     #final_str+="(define-fun skeleton () Bool " + encode_into_mathsat_format(constraint)+")\n"
     #final_str+="(assert skeleton)\n(check-sat)\n(exit)"
     input_file_name_split = gd.input_filename.split("/")
     delta_filename="smt2_files/"+input_file_name_split[len(input_file_name_split) - 1].rstrip(".fml").rstrip(".smt2")+"_iter_"+str(gd.iteration)+"_delta.smt2"
     f1=open(delta_filename,"w")
     f1.write(delta_constraint)
     f1.close()
     #if(0 != direction):
     # print "Aborting"
     # exit(1)
       #print final_str
   else:# "REALIZER" == D_SOLVER
   # START OF REALIZER ENCODING COMMENTED OUT
   ## call and get back Realizer encoding (just the translator, don't call z3 as yet) of constraint1 and \not constraint2
     ps = subprocess.Popen(('echo', constraint), stdout=subprocess.PIPE)
   #global TRANSLATOR_CFG_FP
     TRANSLATOR_CFG_FP="examples/single-prec-modified2.cfg"
     myprint("I'm using for delta constraint this file: "+TRANSLATOR_CFG_FP)
     output = subprocess.check_output((TRANSLATOR_PATH,TRANSLATOR_CFG_FP,'var-list.txt'), stdin=ps.stdout)#USE appropriate CONFIG file acc to PRECISION/RANGE
     ps.wait()
     myprint("Translator-expts o/p: "+output)
     output = output.replace("(check-sat)\n(get-model)","")
     if (0==direction):#attempting to increase the variable; delta should be positive
      output+="(assert (fp.gt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
    #two lines below commented out for elimintaing min-delta
    #output+="(assert (=> (>= (- delta (/ 1.0  two-to-exp-p-minus-e-delta)) "+LEAST_NUM+") (= pred-delta (- delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
    #output+="(assert (=> (< (- delta (/ 1.0  two-to-exp-p-minus-e-delta)) "+LEAST_NUM+") (= pred-delta 0.0)))\n"
     else:#attempting to decrease the variable; delta should be negative
      output+="(assert (fp.lt delta ((_ to_fp 8 24) (_ bv0 32))))\n"
    #below two lines commented out for eliminating min-delta
    #output+="(assert (=> (<= (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)) (- "+LEAST_NUM+")) (= pred-delta (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
    #output+="(assert (=> (> (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)) (- "+LEAST_NUM+")) (= pred-delta 0.0)))\n"

   #output+="(assert (=> (> delta 0.0) (= pred-delta (- delta (/ 1.0  two-to-exp-p-minus-e-delta)))))\n"
   #output+="(assert (=> (< delta 0.0) (= pred-delta (+ delta (/ 1.0  two-to-exp-p-minus-e-delta)))))"
     output+="\n(check-sat)\n(get-model)"
     f1=open("z3-delta-constraint.smt2","w")
     f1.write(output)
     f1.close()
   #END OF REALIZER ENCODING COMMENTED OUT
   #print "Start: "+output
   #ps2 = subprocess.Popen(('echo', output), stdout=subprocess.PIPE)
   #ps2.wait()
   if "MATHSAT" == D_SOLVER:
     try:
      myprint("Calling mathsat on small formula to get delta: ")
      ferror=open("debug.smt2","w")
      ferror.write(delta_constraint)
      ferror.close()
      myprint(ctime())
      t1=time()
      #ps2 = subprocess.Popen(('cat', 'mathsat-delta-constraint.smt2'), stdout=subprocess.PIPE)
      #ps2.wait()
      #output2 = subprocess.check_output(('mathsat','-theory.fp.mode=0','-theory.eq_propagation=false','-printer.fp_number_format=0','-model'),stdin=ps2.stdout,stderr=subprocess.STDOUT)
      force_lower_to = False
      #to_str = ""
      if(True):#('Linux'==platform.system()):
       time_left = float(gd.overall_timeout) - float(t1 - gd.start_time)
       if time_left < 0:
        myprint("Overall timeout exceeded before inner loop in iteration "+str(gd.iteration))
        print_final(gd)#TODO:enhance to stats printing
       if(time_left < float(gd.inner_timeout)):
        to = str(time_left)
        force_lower_to = True
        #to_str = "T"
       else:
        to = gd.inner_timeout

       output2 = subprocess.check_output(('timeout',to,'mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=0','-theory.fp.bit_blast_mode=1' ,'-model',delta_filename), stderr=subprocess.STDOUT)
       myprint("delta_filename: "+delta_filename)
       myprint("Mathsat output:\n"+output2)
       #exit(1)
      else:
       output2 = subprocess.check_output(('mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=0','-theory.fp.bit_blast_mode=1' ,'-model', delta_filename), stderr=subprocess.STDOUT)
       myprint("Mathsat output:\n"+output2)
      if ("unsat"==output2[0:5]):
        t2=time()
        fstat.write("%.2fsN\t" % (t2 - t1))
        myprint(ctime())
        myprint(output2)
        msg="UNSATISFIABLE delta constraint for "+gd.input_filename+" during iteration "+str(gd.iteration)
        myprint(msg)
        fdbg=open(gd.molly_debug_file,"a")
        fdbg.write(msg+"\n")
        fdbg.close()
        return {}#mpfr('0')#Fraction(0,1)
      t2=time()
      fstat.write("%.2fs\t" % (t2 - t1))
      print(ctime())
      #exit(1)
      #NOTE: selection policy will be 1 here; if-then-else redundant!
      if(0 == gd.var_selection_policy):
        delta_list = parse_mathsat_output(output2,['delta'],"unsigned_int",gd)
      elif(1 == gd.var_selection_policy):
        list_to_read_back = []
        for var in self.get_arith_vars():
          list_to_read_back += ['delta_'+var.name]
        delta_list = parse_mathsat_output(output2,list_to_read_back,"unsigned_int",gd)
      elif(2 == gd.var_selection_policy):
        myprint("Not yet implemented\n");exit(1)
      elif(5 == gd.var_selection_policy):
        list_to_read_back = []
        for var in inv_arith_vars:
          list_to_read_back += ['delta_'+var.name]
        delta_list = parse_mathsat_output(output2,list_to_read_back,"unsigned_int",gd)
      else:
        myprint("Not yet implemented\n");exit(1)
      print "delta_list"
      print delta_list
      delta_assn = {} #This is the delta assignment dictionary to be returned
      if(None==delta_list or "error"==delta_list):
        delta = mpfr('0')#Fraction(0,1)
        myprint("Mathsat for delta: UNKNOWN")
        t2=time()
        fstat.write("%.2fsU\t" % (t2 - t1))
      else:
        for delta_var in delta_list.keys():
          delta = delta_list[delta_var]
          myprint("delta (unsigned int) = "+delta)
          ps3 = subprocess.Popen(('echo', delta), stdout=subprocess.PIPE)
          output3 = subprocess.check_output(('scripts/to_decimal'), stdin=ps3.stdout)#USE appropriate CONFIG file acc to PRECISION/RANGE
          ps3.wait()
          myprint(output3)
        #delta = "{0:.165Df}".format(output3)
        #delta = Fraction(output3)#mpfr(Fraction(output3))?: Oct 14
          delta = mpfr(mpq(output3))
          myprint(delta_var+": ")
          print delta
          delta_assn[delta_var] = delta
        #myprint("delta (decimal): ")
        #myprint(delta)
        #exit(1)
     except subprocess.CalledProcessError:
      t2=time()
      if(force_lower_to):
       fstat.write("%.2fsT\t" % float(to))
       print_final(gd)
      else:
       fstat.write("%.2fst\t" % (t2 - t1))

      delta = mpfr('0')#Fraction(0,1)
      delta_assn = {}
      #myprint("Mathsat for delta: UNKNOWN")

      fstat.write("%.2fsU\t" % (t2 - t1))
     except MyError as e:
      myprint(e)
      delta = mpfr('0')#Fraction(0,1)
      delta_assn = {}
      t2=time()
      fstat.write("%.2fsE\t" % (t2 - t1))
      #exit(0)
     fstat.flush()
     os.fsync(fstat)
     return delta_assn

   else:#z3 is the solver: PARSING NOT CHANGED FOR MULTIPLE DELTA VARS: WILL NOT WORK NOW
     try:
      myprint("Calling z3 on small formula to get delta: ")
      ferror=open("debug.smt2","w")
      ferror.write(output)
      ferror.close()
      myprint(ctime())
      t1=time()
      output2 = subprocess.check_output(('z3','-st','-smt2','-T:'+str(Z3_DELTA_TIMEOUT),'z3-delta-constraint.smt2'),stderr=subprocess.STDOUT)
      t2=time()
      fstat.write("%.2fs\t" % (t2 - t1))
      myprint(ctime())
    #print output2
      delta_list = parse_solver_output(output2,['delta'])
      myprint("delta_list")
      myprint(delta_list)
      delta = delta_list['delta']
      myprint("DELTA: ")
      myprint(delta)
     except subprocess.CalledProcessError:
      delta = Fraction(0,1)
      myprint("z3 for delta: UNKNOWN")
      t2=time()
      fstat.write("%.2fsU\t" % (t2 - t1))
     except MyError as e:
      myprint(e)
      delta = Fraction(0,1)
      t2=time()
      fstat.write("%.2fsO\t" % (t2 - t1))
      #exit(0)
     fstat.flush()
     os.fsync(fstat)
     return delta

  #returns True only if no operator got refined (i.e. refine() failed)
  #make this adaptive based on previous iteration result, time taken to solve,
  #: ADJUST exponent and mantissa refinement based on that, as well as the timeout
  def refine(self, is_unsat, gd):
    print("Inside refine, abstraction is "+gd.abstraction)
    print "Refine() in PropExp for lfp"
    not_refined = True
    new_precision = gd.precision + gd.refine_prec_inc # increase precision by a configure amount refine_prec_inc
    new_exponent = gd.exponent + gd.refine_exp_inc
    if (gd.precision < gd.max_precision):#will precision be refined?
     not_refined = False #will be refined
     if (new_precision <= gd.max_precision):
      gd.precision = new_precision #refined by the full increment
     else:
      gd.precision = gd.max_precision # refined but only toreach the maximum
    if(gd.exponent < gd.max_exponent):
     not_refined = False
     if new_exponent <= gd.max_exponent:
      gd.exponent = new_exponent
     else:
      gd.exponent = gd.max_exponent

    return not_refined
    #return True #refinement failed


  def expand(self):
    ps = subprocess.Popen(('echo', self.preorder()), stdout=subprocess.PIPE)
    #global TRANSLATOR_CFG_MIXED
    #print "MIXED CFG: " +TRANSLATOR_CFG_MIXED
    TRANSLATOR_CFG_HARDCODED="examples/hardcoded-negative.cfg"
    myprint("lazy encoding translator")
    myprint(ctime())
    myprint("For expanding for top-level call, I'm using "+ TRANSLATOR_CFG_HARDCODED)
    output = subprocess.check_output((TRANSLATOR_PATH,TRANSLATOR_CFG_HARDCODED,'var-list.txt'), stdin=ps.stdout)#USE appropriate CONFIG file acc to PRECISION/RANGE
    myprint(ctime())
    ps.wait()
    return output


def bits_to_int(bit_str):
 exp = 0
 length = len(bit_str)
 for i in range(0, length):
   exp += (2**i) * int(bit_str[length-i-1])
 return exp

#checks if the input str is all zeroes
def all_zeroes(i_str):
  for i in range(0, len(i_str)):
    if ("0"!=i_str[i]):
      return False
  return True

def power2_mpq(base, exp):
 base_mpq = mpq(base)
 res_mpq = mpq(1,1)
 if(exp < 0):
  uexp = -exp
  for i in range(1, uexp+1):
   res_mpq = div(res_mpq, base_mpq)
 else:
  uexp = exp
  for i in range(1, uexp+1):
   res_mpq = mul(res_mpq, base_mpq)
 return res_mpq

def sem_to_decimal(sem, gd):
 #myprint(sem)
 #exit(1)
 if ("true" == sem):
  return True
 elif("false" == sem):
  return False
 bias = 2**(gd.exponent - 1) - 1 # CHANGED TO below just to check mixed precision FPA
 #print "old bias: "+str(bias)
 bias = 2**(len(sem[1])-1) - 1
 #print "new bias: "+str(bias)
 #TODO: not necessary if set elsewhere but check that the below mpfr's context is set to appropraite prec and mantissa
 #old solve_rp.py computed_exp = mpfr(bits_to_int(sem[1]) - bias) #computed_exp is the unbiased exponent, which may be negative
 computed_exp = bits_to_int(sem[1]) - bias
 #print "computed_exp: "
 #print computed_exp
 ctx = get_context()
 #print ctx
 #ctx.precision = 4
 if(all_zeroes(sem[1]) and all_zeroes(sem[2])):
   return mpq(0,1)#mpfr('0')
 #also check for denormal numbers
 if(all_zeroes(sem[1])):#subnormal/denormal number
   computed_exp = computed_exp + 1
   #print computed_exp
   print_error_msg(gd," Caution! Subnormal number found\n")
   #val = mpfr('0')# old solve_rp.py
   val = mpq(0,1)
   #for i in range(0,gd.exponent):
   #  val+= mpfr(sem[2][i]) * (mpfr('2.0')**(computed_exp - i - 1))
 else:
   #val = 2**float(computed_exp)#for the assumed leading 1 that is omitted in IEEE mantissa
   #old solve_rp.py val = mpfr('2.0')**computed_exp#for the assumed leading 1 that is omitted in IEEE mantissa
   val = power2_mpq(2,computed_exp)
   #val = mpfr('2')**mpfr(computed_exp)
   #print "Value after each iteration: "
 #for i in range(0,gd.precision):
 #print "Old vs new prec: "+str(gd.precision)+" vs. "+str(len(sem[2]))
 for i in range(0,len(sem[2])):
   #old solve_rp.py val+= mpfr(sem[2][i]) * (mpfr('2.0')**(computed_exp - i - 1))
   val = add(val, mul(mpq(sem[2][i]), power2_mpq(2, (computed_exp - i - 1))))
 #print get_context()#ideally this should be lower prec
 #exit(1)
 #TODO: emax, emin should also be assigned appropriately
 #print "{0:.165Df}".format(val)
 if ("0" == sem[0]):
  return val
 else:# sign is 1, negative number
  #old solve_rp.py return mpfr('-1.0') * val
  return mul(mpq(-1,1),val)#without the mpfr is the actual rational value

def sem_to_decimal_old(sem, gd):
 myprint(sem)
 #exit(1)
 if ("true" == sem):
  return True
 elif("false" == sem):
  return False
 bias = 2**(gd.exponent - 1) - 1
 #print "bias: "
 print bias
 #TODO: not necessary if set elsewhere but check that the below mpfr's context is set to appropraite prec and mantissa
 computed_exp = mpfr(bits_to_int(sem[1]) - bias) #computed_exp is the unbiased exponent, which may be negative
 #print "computed_exp: "
 #print computed_exp
 ctx = get_context()
 #ctx.precision = 4
 if(all_zeroes(sem[1]) and all_zeroes(sem[2])):
   return mpfr('0')
 #also check for denormal numbers
 if(all_zeroes(sem[1])):#subnormal/denormal number
   computed_exp = computed_exp + 1
   print computed_exp
   print_error_msg(gd," Caution! Subnormal number found\n")
   val = mpfr('0')#mpfr('2.0')**computed_exp
   #for i in range(0,gd.exponent):
   #  val+= mpfr(sem[2][i]) * (mpfr('2.0')**(computed_exp - i - 1))
 else:
   #val = 2**float(computed_exp)#for the assumed leading 1 that is omitted in IEEE mantissa
   val = mpfr('2.0')**computed_exp#for the assumed leading 1 that is omitted in IEEE mantissa
   #val = mpfr('2')**mpfr(computed_exp)
   #print "Value after each iteration: "
 for i in range(0,gd.exponent):
   val+= mpfr(sem[2][i]) * (mpfr('2.0')**(computed_exp - i - 1))
    #print "{0:.165Df}".format(val)
    #print "{0:.165Df}".format(val)
 #print get_context()#ideally this should be lower prec
 #exit(1)
 #TODO: emax, emin should also be assigned appropriately
 if ("0" == sem[0]):
  return val
 else:# sign is 1, negative number
  return mpfr('-1.0') * val

def parse_mathsat_output(output2,listofvars,op_format,gd):
 #myprint("Inside mathsat_parse:")
 outputstring = ""
 mathsatoutput=output2

 if(mathsatoutput[0:5] == "unsat"):
   myprint("Unsat\n")
   #result, assignment = ("Unsat",None)
   return None
   #sys.exit(1)
 if(mathsatoutput[0:6] == "(error"):
   myprint("mathsat output Error\n")
   return "error"
   #sys.exit(1)
 myprint("Sat")
 assignment = {}
 if "unsigned_int" == op_format:#assuming bitvector of size 32
  for var in listofvars:#change
    assignment[var]=constructrowmathsatsmtlib(mathsatoutput,var)
 elif "sme" == op_format:#(Sign, Exponent, Mantissa)
  for var in listofvars:
    assignment[var]=sem_to_decimal(constructrowmathsatsmtlib2(mathsatoutput,var,gd),gd)
 myprint("Read back mathsat assignment")
 #print assignment
 #exit(1)
 return assignment

def parse_dreal_output(output2, listofvars):
 assignment = {}
 return assignment

def parse_solver_output(output2,listofvars, solver):
 myprint("Inside z3/dreal output parser:")
 outputstring = ""
 solver_output=output2
 #listofvars=['delta']
 #inputlines = sys.stdin.readlines()

 #for line in inputlines:
 #  solver_output+=line
 if (solver_output[0:7] == "unknown"):
   myprint("Unknown\n")
   return Fraction(0,1)
   #sys.exit(1)
 if(solver_output[0:7] == "timeout"):
   print("Timeout\n")
   #return {'delta':Fraction(0,1)}
   raise MyError("z3 timed out")
   #sys.exit(1)
 if(solver_output[0:5] == "unsat"):
   print("Unsat\n")
   return Fraction(0,1)
   #sys.exit(1)
 if(solver_output[0:6] == "(error"):
   print("z3 output Error\n")
   sys.exit(1)
   #elif (string.find(solver_output,"(error")!=-1):
    # print ("Error\n")
     #sys.exit(1)
   #print solver_output
 myprint("Sat")
 #for var in listofvars:
 # outputstring += str (constructrow(solver_output,var)) +"\n"
 assignment = {}
 for var in listofvars:
   if("z3" == solver):
     assignment[var]=constructrow(solver_output,var)
   else:# solver = "dreal"
     assignment[var]=constructrow_dreal(solver_output,var)
 myprint("Printing assignment:")
 myprint (assignment)
 #return constructrow(solver_output,'delta')
 #print outputstring
 #print assignment
 return assignment

def constructrow_dreal(drealoutput, var):
  #myprint("The variable is "+var)
  rowstart=drealoutput.find(var+" : ")
  if(-1 == rowstart):
    myprint("Variable "+var +" not found in dReal's output")
    return Fraction(0,1)
  rowequal = drealoutput[rowstart:].find("= [")
  rowend = drealoutput[rowstart:].find("\n")
  comma_pos = drealoutput[rowstart+rowequal:].find(",")
  lower_bound = drealoutput[(rowstart+rowequal+3): (rowstart + rowequal+ comma_pos)]
  #myprint("rowequal:" +str(rowequal))
  #myprint("comma_pos: "+str(comma_pos))
  #myprint("rowequal:" +str(rowequal))
  #myprint("rowend:" +str(rowend))
  #myprint("The lower_bound value is "+lower_bound)
  #exit(0)
  return Fraction(lower_bound)
# constructrow for parsing z3's output
def constructrow(z3output, var):
   rowstring = ""
   #print "z3output= "+z3output+ "\nvar = "+ var
   leftindex = string.find(z3output,"(define-fun "+ var + " () ")
   if (-1 == leftindex):
     myprint ("ERROR in constructrow() : variable"+ var +" not found")
     return var+ " " + "not found"
   #print "leftindex = " + str(leftindex)+"\n"
   rightindex = string.find(z3output[leftindex:],")\n")
   #print "rightindex= "+str(rightindex)
   temp = z3output
   #print temp
   divisioncell=""
   #divisioncell=temp[leftindex+17+len(var):leftindex+rightindex].split("\n")[1].lstrip(" ")#commented by Jaideep
   new_temp = temp[leftindex+25+len(var):]
   new_right_index= new_temp.find(")")#02/28
   divisioncell = new_temp[:new_right_index+1]
   print "divisioncell: "
   print divisioncell
   split_value = divisioncell.lstrip("(").rstrip(")").split(" ")#commented by Jaideep
   print "split_value: "
   print split_value
   if(1 == len(split_value)):#no denominator, so adding 1.0 as denominator
    split_value+=["/"]
    split_value[1]=split_value[0]
    split_value[0]="/"
    split_value+=["1.0"]
    divisioncell=divisioncell.rstrip(")")
   else:
     if (2== len(split_value) and '-' == split_value[0]):
      split_value+=["1.0"]
      split_value+=["1.0"]
      split_value[2] = split_value[1]
      split_value[1] = '/'
   #print split_value[1].rstrip("\n").rstrip(".0")+ "/"+ split_value[len(split_value)-1].rstrip(".0")
   #print "Check: "+str(split_value[1].rstrip("\n").rstrip("0").rstrip("."))
   if ('-'==split_value[0]):
     numerator = '-'+split_value[2].rstrip("\n").rstrip("0").rstrip(".")
   else:
     numerator = split_value[1].rstrip("\n").rstrip("0").rstrip(".")
   denominator = split_value[len(split_value)-1].rstrip("0").rstrip(".")
   rowstring+= "(assert (= "+var+" "+divisioncell+"))"
   myprint(rowstring)
   myprint("Var: "+var+" \nNumerator:")
   print numerator
   myprint("Denominator: ")
   print denominator
   #components = divisioncell.split(" ")
   #print components[1],components[0],components[2]
   #return divisioncell
   return Fraction(Fraction(numerator),Fraction(denominator))
   #return Fraction(Fraction(split_value[1].rstrip(".0")),Fraction(split_value[2].rstrip(".0")))

##( (delta ((_ to_fp 8 24) (_ bv218103801 32))) )
def constructrowmathsatsmtlib(mathsatoutput, var):
   myprint("Inside constructrowmathsatsmtlib")
   rowstring = ""
   #print "z3output= "+z3output+ "\nvar = "+ var
   leftindex = string.find(mathsatoutput,"("+ var+ " ")
   if (-1 == leftindex):
     myprint("ERROR in constructrowmathsat() : variable not found")
     exit(1)
     return var+ " " + "not found"
   #print "leftindex = " + str(leftindex)+"\n"
   rightindex = string.find(mathsatoutput[leftindex:],"))")
   newleftindex = mathsatoutput[leftindex:].find("bv")
   deltastring = mathsatoutput[leftindex+newleftindex+2:leftindex+rightindex-3]
   myprint("Unsigned int delta = "+deltastring)
   #exit(1)
   return deltastring

def n_ones(n):
  ret_str = ""
  for i in range(0,n):
    ret_str+="0"
  return ret_str

def n_ones(n):
  ret_str = ""
  for i in range(0,n):
    ret_str+="1"
  return ret_str

def constructrowmathsatsmtlib2(mathsatoutput, var,gd):
   #myprint("Inside constructrowmathsatsmtlib2: "+str(var))
   rowstring = ""
   if(gd.enable_abstract_check):
     leftindex = string.find(mathsatoutput,")) )")+5
     mathsatoutput = mathsatoutput[leftindex:]
     #print mathsatoutput
     #exit(1)
   leftindex = string.find(mathsatoutput,"("+ var+ " ")
   if (-1 == leftindex):
     myprint("ERROR in constructrowmathsatsmtlib2() : variable not found")
     return var+ " " + "not found"
   #print "leftindex = " + str(leftindex)+"\n"
#   sat
#( (a1 (fp #b0 #b000 #b001))
#  (a2 (fp #b1 #b011 #b000))
#  (a3 (fp #b0 #b010 #b100)) )
#(a1 ((_ to_fp 3 4) (_ bv1 7)))
#  (a2 ((_ to_fp 3 4) (_ bv88 7)))
#  (a3 ((_ to_fp 3 4) (_ bv20 7)))
   rightindex = string.find(mathsatoutput[leftindex:],")")
   newleftindex = mathsatoutput[leftindex:(leftindex+rightindex+2)].find("(fp")
   if(-1 == newleftindex):# plus or minus inf or error
     if(gd.enable_abstract_check):
       boolean_str = mathsatoutput[(leftindex+1+len(var)):(leftindex+rightindex)].strip()
       myprint("Boolean: "+boolean_str)
       if("true" == boolean_str or "false" == boolean_str):
        return boolean_str
     myprint("Special value being parsed: "+mathsatoutput[leftindex:(leftindex+rightindex+2)])
     if (-1 != mathsatoutput[leftindex:(leftindex+rightindex+2)].find("(_ +")): #oo")):
       sem = ("0", n_ones(gd.exponent), n_ones(gd.precision))
       myprint("plus Inf")
     elif (-1 != mathsatoutput[leftindex:(leftindex+rightindex+2)].find("(_ -")): #oo")):
       sem = ("1", n_ones(gd.exponent), n_ones(gd.precision))
       myprint("minus Inf")
     else:
       myprint("Unhandled value output from mathsat")
       exit(1)
   else:#regular number in FP (may be low precision) format
     sem_string = mathsatoutput[leftindex+newleftindex+4:leftindex+rightindex]
     split = sem_string.split(" ")
     #myprint(split)
     sign = split[0].lstrip("#b")
     exp = split[1].lstrip("#b")
     mantissa = split[2].lstrip("#b").rstrip("))")
     sem = (sign, exp, mantissa)
   myprint(sem)
   #exit(1)
   return sem

def constructrowmathsat(mathsatoutput, var):
   myprint("Inside constructrowmathsat")
   rowstring = ""
   #print "z3output= "+z3output+ "\nvar = "+ var
   leftindex = string.find(mathsatoutput,"("+ var+ " ")
   if (-1 == leftindex):
     myprint("ERROR in constructrowmathsat() : variable not found")
     return var+ " " + "not found"
   #print "leftindex = " + str(leftindex)+"\n"
   rightindex = string.find(mathsatoutput[leftindex:],"))")
   newleftindex = mathsatoutput[leftindex:].find(")")
   deltastring = mathsatoutput[leftindex+newleftindex+2:leftindex+rightindex]
   myprint ("Unsigned int delta = "+deltastring)
   #exit(1)
   return deltastring

def smtlib_value(val):
  val_str = "{0:.165Df}".format(val)
  #myprint(val_str)
  if(val < mpfr('0.0')):
    if('-inf' == val_str):
     str = "(fp #b1 #b"+n_ones(8)+" #b"+n_zeroes(23)+")"
    else:
     val = -val
     str = "(- "+"{0:.165Df}".format(val)+")"
  else:#val>mpfr('0.0')
    if('inf' == val_str):
      str = "(fp #b0 #b"+n_ones(8)+" #b"+n_zeroes(23)+")"
    else:
     str = "{0:.165Df}".format(val)
  return str

#checks if the
#returns True or False
def check_fp_values_pylib_solver(propexp, gd):
  myprint("Inside check_fp_values_pylib_solver")
  gd.checking_phase = True
  #Generate SMT-LIB formula file for full precision
  ctx = get_context()
  ctx.precision = 24; ctx.emax = 128; ctx.emin = -148; ctx.subnormalize =  True #also change emax and emin
  set_context(ctx)
  saved_exponent = gd.exponent
  saved_precision = gd.precision
  gd.exponent = 8
  gd.precision = 23
  saved_gd_generate_benchmark_real = gd.generate_benchmark_real
  saved_gd_abstraction = gd.abstraction
  gd.generate_benchmark_real = False
  gd.abstraction = "lfp"
  constraint = gd.generate_smtlib_fp()+"(assert propexp)\n"
  gd.abstraction = saved_gd_abstraction
  gd.generate_benchmark_real = saved_gd_generate_benchmark_real
  gd.exponent = saved_exponent
  gd.precision = saved_precision
  #Insert the full precision FP assignment assertions to all arith vars: these are in var.fp_val \forall var \in Var
  common_smtlib ="((_ to_fp 8 24) RNE "
  for var in propexp.get_arith_vars():
    constraint += "(assert (= "+ var.name + " " + common_smtlib + smtlib_value(var.fp_val)+")))\n"
  constraint+="(check-sat)\n(exit)"
  #Call SMT-LIB solver with above constraint
  fpcheck = open("fp_check.smt2","w")
  fpcheck.write(constraint)
  fpcheck.close()
  #myprint(constraint)
  #output2 = subprocess.check_output(('mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=1','-theory.fp.bit_blast_mode=1' ,'-model',"fp_check.smt2"), stderr=subprocess.STDOUT)
  output2 = subprocess.check_output(('z3','-smt2','fp_check.smt2'), stderr=subprocess.STDOUT)
  myprint(output2[:5])
  if ("sat" == output2.strip()[0:3]):
   if(propexp.fp_eval == False):
    myprint(" MISMATCH: check_fp reveals we/pylib evaluated propexp to False but z3 evaluates FP assignment to True")
    print_error_msg(gd, " MISMATCH: check_fp reveals we/pylib evaluated propexp to False but z3 evaluates FP assignment to True\n")
    if(gd.enable_strict_consis_check):
     exit(1)
   #else:
   #  return True
  elif("unsat" == output2.strip()[0:5]):
   if(gd.delta_obtained):
     print_error_msg(gd, " a value for delta was obtained but z3 evaluates FP assignment to False\n")
     if(gd.enable_strict_consis_check):
      exit(1)
     gd.delta_obtained = False
   if(propexp.fp_eval == True):
    myprint(" MISMATCH: check_fp reveals we/pylib evaluated propexp to True but z3 evaluates FP assignment to False")
    print_error_msg(gd, " MISMATCH: check_fp reveals we/pylib evaluated propexp to True but z3 evaluates FP assignment to False\n")
    if(gd.enable_strict_consis_check):
     exit(1)
   #else:
   # return True
  else:
    myprint("Error in check_fp")
    if(gd.enable_strict_consis_check):
     exit(1)
  #If result is not the same as propexp.fp_val, then we have a problem, else fine
  gd.checking_phase = False
  return True

def check_abstract_values_pylib_solver(propexp, gd):
  ret_val = True
  myprint("Inside check_abstract_values_pylib_solver")
  objects = gd.ordered.keys()
  for obj in objects:
    if(isinstance(obj, Var) or isinstance(obj, Const)):
     #myprint(obj.name)
     #myprint(obj.abstract_val)
     if(obj.abstract_val != obj.abstract_solver_val):
      myprint(" Error in abstract_val for Var/Const variable "+obj.name)
      print_error_msg(gd, " Error in abstract_val for Var/Const variable "+obj.name+" in iteration "+str(gd.iteration)+"\n")
      print_error_msg(gd, "{0:.165Df}".format(obj.abstract_solver_val)+" (solver) vs. "+"{0:.165Df}".format(obj.abstract_val))
      #print_error_msg(gd,str(type(obj.abstract_val)))
      print "{0:.165Df}".format(obj.abstract_solver_val)+" (solver) vs. " + "{0:.165Df}".format(obj.abstract_val)
      #print_error_msg(gd, " {0:.165Df}".format(obj.abstract_solver_val)+" (solver) vs. " + "{0:.165Df}".format(obj.abstract_val)+"\n")
      print obj.abstract_val
      sys.stdout.flush()
      #exit(1)
      if(gd.enable_strict_consis_check):
       exit(1)
      #exit(1)
      ret_val = False
    elif(isinstance(obj, ArithExp)):
     #myprint(obj.name)
     #myprint(obj.abstract_val)
     if(obj.abstract_val != obj.abstract_solver_val):#comparison of numerical abstract values, obj.abstract_val has been computed internally by the gmpy2
      myprint(" Error in abstract_val for ArithExp variable " + obj.name)
      print_error_msg(gd, " Error in abstract_val for ArithExp variable "+obj.name+" in iteration "+str(gd.iteration)+"\n")
      print "{0:.165Df}".format(obj.abstract_solver_val)+" (solver) vs. " + "{0:.165Df}".format(obj.abstract_val)
      print_error_msg(gd," {0:.165Df}".format(obj.abstract_solver_val)+" (solver) vs. " + "{0:.165Df}".format(obj.abstract_val)+"\n")
      if(gd.enable_strict_consis_check):
       exit(1)
      #exit(1)
      ret_val = False
    elif(isinstance(obj, Prop) or isinstance(obj, PropExp)):
     if(obj.abstract_eval != obj.abstract_solver_eval):#comparison of Booleans
      myprint("\nError in abstract_eval for Prop/PropExp variable " +obj.name+" in iteration "+str(gd.iteration)+"\n")
      print_error_msg(gd," Error in abstract_eval for Prop/PropExp variable "+obj.name+" in iteration "+str(gd.iteration)+"\n")
      print "IMPORTANT: "+str(obj.abstract_solver_eval)+" (solver) vs. " + str(obj.abstract_eval)+"\n"
      print_error_msg(gd," IMPORTANT: "+str(obj.abstract_solver_eval)+" (solver) vs. " + str(obj.abstract_eval)+"\n")
      if(gd.enable_strict_consis_check):
       exit(1)
      #exit(1)
      ret_val = False
    #elif()
    else:
     myprint("Inside check_abstract_values_pylib_solver(): Obj is not any of Var, Const, ArithExp, Prop, PropExp in iteration "+str(gd.iteration)+"\n")
     print obj
     if(gd.enable_strict_consis_check):
      exit(1)
     ret_val = False
  return ret_val

   #return Fraction(Fraction(split_value[1].rstrip(".0")),Fraction(split_value[2].rstrip(".0")))
#Check: z3/parsing back seems to fail with this
def invert_rel_expr_str(str):
 if (-1 < str.find(">=")):
  str=str.replace(">=","<")
 elif (-1 < str.find("<=")):
  str=str.replace("<=",">")
 elif (-1 < str.find(">")):
  str=str.replace(">","<=")
 elif (-1 < str.find("<")):
  str =str.replace("<",">=")
 elif (-1 < str.find("=")):
  str = "(not "+ str + ")"
 #print "Returning the not as : "+"(not "+str+")"
 #return "(not "+str+")"
 return str

#compute (quantitative) upward support provided by var for prop
def get_delta_us(var,prop,ctx):
 #CR: check FP settings;
 #CR: which calculations to do in rp, FP or more precise/Fraction()?
 # computing the next 'k'  FP values
 #print "k =" +str(k)
 right_next = []
 right_next.append(var.fp_val)
 right_val = []
 right_val.append(mpfr('0'))
 #at_val for bothe left and right, and their diff
 at_val_left = Fraction(str(evaluate_fp_at(prop.rel_exp.left, var, var.fp_val)))#
 at_val_right = Fraction(str(evaluate_fp_at(prop.rel_exp.right, var, var.fp_val)))#))))
 delta_us = Fraction('0')

 for i in range(1,k+1):
   right_next.append(get_next_fp(right_next[i-1],ctx))
   #right_val.append((Fraction(str(evaluate_fp_at(prop.rel_exp.left, var, right_next[i]))) - at_val)/Fraction(str(i)))
   right_val.append(((Fraction(str(evaluate_fp_at(prop.rel_exp.left, var, right_next[i]))) - at_val_left)
       - (Fraction(str(evaluate_fp_at(prop.rel_exp.right, var, right_next[i]))) - at_val_right)))#/Fraction(str('i')))
   delta_us += right_val[i]

 myprint ("{0:.165Df}".format(right_next[1]))
 myprint ("{0:.165Df}".format(right_next[2]))
 #print right_val
 #right_next1 = get_next_fp(var.fp_val,ctx)
 #right_next2 = get_next_fp(right_next1,ctx)
 #right_next3 = get_next_fp(right_next2,ctx)
 # computing value at next 'k' FP values
 #at_val = evaluate_fp_at(prop.rel_exp.left, var, var.fp_val)
 #right_val1 = evaluate_fp_at(prop.rel_exp.left, var, right_next1) - at_val
 #right_val2 = evaluate_fp_at(prop.rel_exp.left, var, right_next2) - at_val
 #right_val3 = evaluate_fp_at(prop.rel_exp.left, var, right_next3) - at_val
 #delta_us = (right_val1 + right_val2 + right_val3)#/mpfr('3')#the operations are from FP(r,p)

 #DIFF f(Succ(x)) - g(Succ(x)) go from mpfr to Real?
 #print var.name+": "+ prop.name+" "+str(delta_us)

 if('M' == prop.type):
  if(mpfr(0) < delta_us):#need to use \epsilon?:)
   delta_us = Fraction('1')#"plus"#positive
  else:
   delta_us = Fraction('-1')
 return delta_us

def get_delta_ds(var,prop,ctx):
 # computing the prev 'k' FP values
 #print "k =" +str(k)
 #CR: check FP settings;
 #CR: which calculations to do in rp, FP or more precise/Fraction()?
 left_prev = []
 left_prev.append(var.fp_val)
 left_val = []
 left_val.append(mpfr('0'))
 at_val_left = Fraction(str(evaluate_fp_at(prop.rel_exp.left, var, var.fp_val)))#
 at_val_right = Fraction(str(evaluate_fp_at(prop.rel_exp.right, var, var.fp_val)))#))))
 delta_ds = Fraction('0')

 for i in range(1,k+1):
   left_prev.append(get_prev_fp(left_prev[i-1],ctx))
   left_val.append(((Fraction(str(evaluate_fp_at(prop.rel_exp.left, var, left_prev[i]))) - at_val_left)
       - (Fraction(str(evaluate_fp_at(prop.rel_exp.right, var, left_prev[i]))) - at_val_left)))#/Fraction(str('i')))
   delta_ds += left_val[i]
 #print left_prev
 #print left_val
 # at_val = Fraction(str(evaluate_fp_at(prop.rel_exp.left, var, var.fp_val)))#reqd only for f(x) op c
 # delta_ds = Fraction('0')
 # for i in range(1,k+1):
 #   left_prev.append(get_next_fp(left_prev[i-1],ctx))
 #   #left_val.append((Fraction(str(evaluate_fp_at(prop.rel_exp.left, var, left_prev[i]))) - at_val)/Fraction(str(i)))
 #   left_val.append((Fraction(str(evaluate_fp_at(prop.rel_exp.left, var, left_prev[i]))) - Fraction(str(evaluate_fp_at(prop.rel_exp.right, var, left_prev[i]))))/Fraction(str(i)))
 #   delta_ds += left_val[i]
 ##left_prev1 = get_prev_fp(var.fp_val, ctx)
 ##print "prev1:"
 ##print left_prev1
 ##left_prev2 = get_prev_fp(left_prev1, ctx)
 ##print left_prev2
 ##left_prev3 = get_prev_fp(left_prev2, ctx)
 ##print left_prev3
 #at_val = evaluate_fp_at(prop.rel_exp.left, var, var.fp_val)
 ## computing value at next 'k' FP values
 ##left_val1 = evaluate_fp_at(prop.rel_exp.left, var, left_prev1) - at_val
 ##left_val2 = evaluate_fp_at(prop.rel_exp.left, var, left_prev2) - at_val
 ##left_val3 = evaluate_fp_at(prop.rel_exp.left, var, left_prev3) - at_val
 ##delta_ds = (left_val1 + left_val2 + left_val3)#/mpfr('3')#the operations are from FP(r,p)
 if('M' == prop.type):
  if (mpfr(0) < delta_ds):#need to use \epsilon?:)
   delta_ds = Fraction('1')#"plus"#positive
  else:
   delta_ds = Fraction('-1')

 #print var.name+": "+ prop.name+" "+str(delta_ds)
 return delta_ds


# check this again for boundary cases, write a theorem
def get_next_fp(val,ctx):
  #assume val fits in the fp format
  #compute the value to be added: (2^{-prec+1}) * (2^exponent)
  next_fp = val+sign(val)*exp2(floor(log2(abs(val))))*exp2(-ctx.precision+1)#actually +1
  if(next_fp == val):
    if(0 == val):
      next_fp = exp2(-ctx.precision+1)
    if(next_fp == val):
      myprint ("Error in computing next fp")
      myprint ("Value is "+"{0:.165Df}".format(val))
      myprint(get_context())
      exit(1)
  return next_fp

def get_prev_fp(val,ctx):
  #assume val fits in the fp format
  #compute the value to be added: (2^{-prec+1}) * (2^exponent)
  prev_fp = val - sign(val)*exp2(floor(log2(abs(val))))*exp2(-ctx.precision+1)#actually +1
  if (prev_fp == val):
   if(0 == val):
    prev_fp = -exp2(-ctx.precision+1)
    if(prev_fp == val):
      myprint ("Error in computing prev fp")
      myprint ("Value is "+"{0:.165Df}".format(val))
      myprint(get_context())
      exit(1)
  return prev_fp

def uniq(input):
  output = []
  for x in input:
    if x not in output:
      output.append(x)
  return output

def sort_uniq(input):
    output = []
    for x in input:
      if x not in output:
        output.append(x)
    output.sort()
    return output


def set_prec_mode(precision, mode, ctx):
  ctx.precision = precision
  ctx.round = mode
  set_context(ctx)
  return ctx

def evaluate_prop_real(prop_exp):
  if isinstance(prop_exp,Prop):
    return prop_exp.abstract_eval
  if 'not' == prop_exp.bool_op:
    return not(evaluate_prop_real(prop_exp.left_exp))
  elif 'and' == prop_exp.bool_op:
    return evaluate_prop_real(prop_exp.left_exp) and evaluate_prop_real(prop_exp.right_exp)
  elif 'or' == prop_exp.bool_op:
    return evaluate_prop_real(prop_exp.left_exp) or evaluate_prop_real(prop_exp.right_exp)
  else:#never occurs
    return False

def evaluate_fp(exp):
 if ((exp.left==None)and(exp.right==None)):
  return exp.fp_val
 else:
  if exp.op == '+':
   return evaluate_fp(exp.left) + evaluate_fp(exp.right)
  elif exp.op == '-':
   return evaluate_fp(exp.left) - evaluate_fp(exp.right)
  elif exp.op == '*':
   return evaluate_fp(exp.left) * evaluate_fp(exp.right)
  elif exp.op == '/':
   return evaluate_fp(exp.left) / evaluate_fp(exp.right)
  else:
   return mpfr('0')

def evaluate_fp_at(exp, var, val):
	if(exp==var):
		return val
	elif ((exp.left==None)and(exp.right==None)):
		return exp.fp_val
	else:
		if exp.op == '+':
		 return evaluate_fp_at(exp.left,var,val) + evaluate_fp_at(exp.right,var,val)
		elif exp.op == '-':
		 return evaluate_fp_at(exp.left,var,val) - evaluate_fp_at(exp.right,var,val)
		elif exp.op == '*':
		 return evaluate_fp_at(exp.left,var,val) * evaluate_fp_at(exp.right,var,val)
		elif exp.op == '/':
		 return evaluate_fp_at(exp.left,var,val) / evaluate_fp_at(exp.right,var,val)
		else:
		 return mpfr('0')

# return a prop expression with a redundant set of propostions removed.
# this combines RedundantSet() and Universal Quantification from the paper.
# probably not equivalent to it but good enough for implementation
# TODO: improve efficiency
# ideally should also call propositional simplifier in the end, but not required
def simplify(prop_exp,gd):
 return prop_exp
 if isinstance(prop_exp,Prop) or (None == prop_exp):
  return prop_exp # return the proposition itself
 left = simplify(prop_exp.left_exp,gd)
 right = simplify(prop_exp.right_exp,gd)
 #if op is 'or' and one of the children is TRUE, then the other subtree is pruned
 if (True == prop_exp.abstract_eval) and ('or' == prop_exp.bool_op):
  myprint ("0") #debug code
  if True == prop_exp.left_exp.abstract_eval:
   myprint ("0.0")#debug code
   return left
  elif True == prop_exp.right_exp.idal_eval:
   myprint ("0.1")#debug code
   return right
  #if op is 'and' and one of the children is FALSE, then the other subtree is pruned
 elif (False == prop_exp.abstract_eval) and ('and' == prop_exp.bool_op):
  myprint ("1")#debug code
  if (False == prop_exp.left_exp.abstract_eval):
   myprint ("1.0")#debug code
   return left
  elif (False == prop_exp.right_exp.abstract_eval):
   myprint ("1.1") #debug code
   return right
 myprint("Outside")
 new_propexp_name = prop_exp.name +"_simplify_"+ str(gd.simplify_index)
 gd.increment_simplify_index()
 return PropExp(gd, new_propexp_name,left,prop_exp.bool_op,right)


def generate_pure_real_smt2(formula):
  f1 = open(ARITH_VARS_FILE,"r")
  var_list = f1.readline().rstrip(" ").lstrip(" ").split(" ")
  constraint=""
  for var in var_list:
    constraint+="(declare-const " + var + " Real)\n"
    constraint+="(assert (or (> " + var +" "+ LEAST_NUM+")(< " + var +" -"+ LEAST_NUM+")))\n"
  f1.close()
  constraint+="(assert "+ formula.rstrip("\n") +")\n(check-sat)\n;(get-model)\n"
  return constraint

def convert_to_smtlib_stmts(solver_output):
  return ""

def consistency_check(solver_output, precision, exponent):
  saved_precision = gd.precision # save the current precision for the iteration
  saved_exponent = gd.exponent
  gd.precision = precision + 1
  gd.exponent = exponent
  constraint = gd.generate_smtlib_fp()+"(assert propexp)\n(check-sat)\n(exit)"
  #append the assignment to the generated constraints
  constraint += convert_to_smtlib_stmts(solver_output)#remove "sat\n", add assert, upcast assignment to (8, 24) if reqd, add (check-sat)\n(exit)
  #call an external solver (z3 here) to do the check
  consistency_filename = open("consistency.smt2","w")
  try:
    myprint("Calling z3 to do consistency check on sat assignment")
    output2 = subprocess.check_output(('timeout','60','z3','-smt2',consistency_filename), stderr=subprocess.STDOUT)
  except subprocess.CalledProcessError:
      myprint("Error 1 in z3 call for consistency check")
      consistency_filename.close()
      gd.precision = saved_precision #revert to the iteration precision
      gd.exponent = saved_exponent
      return
  except MyError as e:
      myprint(e)
      myprint("Error 2 in z3 call for consistency check")
      consistency_filename.close()
      gd.precision = saved_precision #revert to the iteration precision
      gd.exponent = saved_exponent
      return
  if(("unsat"!= output2[0:5]) and ("(error" != output2[0:6])):
      myprint("Consistency check passed!")
  consistency_filename.close()
  gd.precision = saved_precision #revert to the iteration precision
  gd.exponent = saved_exponent


#The function that does Model Reconstruction
# takes in a PropExp (real and fp assignments contained in data structure) that
# currently evaluates to false, which it will attempt to make true by nudging arithmetic variable
# assignment
def transform0(final_p,ctx1,gd):
  myprint("All props of final_p: ")
  for p in final_p.get_all_props():
      myprint(p.print2())
  #CR: enable simplify
  final_new = simplify(final_p,gd)
  myprint("Simplified final_p, i.e. final_new: ")
  myprint(final_new.print2())
  if(isinstance(final_new,Prop)):
    final_new.categorize_prop()
    myprint("Categorized the only prop remaining as "+final_new.type+ ", error if M or X!")
  else:
    final_new.categorize_props()#as 'I' or 'M'
  invertibles = final_new.invertibles()
  myprint("Invertibles: ")
  for p in  invertibles:
   myprint(p.print2())
  maintainables = uniq(final_new.maintainables())
  myprint("Maintainables: ")
  for p in maintainables:
   myprint(p.print2())
  if([]==invertibles):
   msg="Error: empty invertible set I for "+gd.input_filename+" during iteration "+str(gd.iteration)
   myprint(msg)
   fdbg=open(gd.molly_debug_file,"a")
   fdbg.write(msg+"\n")
   fdbg.close()
   return final_new
   #exit(1)
  for iteration in range(0,len(invertibles)):#Loops around for maximum |original invertibles| number of times
    #CR: check FP settings here
    final_new.dependency_table(ctx1)
    if 1:#commented on Nov 18 2015
     for var in final_new.get_arith_vars():
       for p in invertibles+maintainables:
         #print "Hello: "+ p.name + " "+p.type+" "+str(var.support[p][0])
         #continue
         myprint(var.name +", Upward support for "+p.name+" (of type "+p.type+"): ")
         #myprint(str(var.support[p][0]))
         myprint(var.name + ", Downward support for "+p.name+" (of type "+p.type+"): ")
         #myprint(str(var.support[p][1]))
         myprint ("")

	  #for var in final_new.get_arith_vars():
	  # print var.name+"'s Upward support for all props is non-neg: "+str(var.all_non_neg(0))
	  # print var.name+"'s Upward support for atleast one invertible prop is pos: "+str(var.one_pos_invertible(0))
	  # print var.name+"'s Downward support for all props is non-neg: "+str(var.all_non_neg(1))
	  # print var.name+"'s Downward support for atleast one invertible prop is pos: "+str(var.one_pos_invertible(1))
    var_dir_prop_selection = final_new.next_var()#
    # Some of the following lines were hardcorded to force var/prop selection for sine.1.0.
    #all_arith_vars = final_new.get_arith_vars()
    #for var in all_arith_vars:
    # if('lit_9'== var.name):
    #  selected = var
    #  break
    #var_dir_prop_selection = (selected,1,10,final_new.invertibles()[0])
    if (None == var_dir_prop_selection[0]):
      myprint ("No suitable next variable could be found for nudging")
      return final_p
    inv_prop_val_before = var_dir_prop_selection[3].fp_eval
    delta = final_new.value_change0(var_dir_prop_selection[0],var_dir_prop_selection[1],var_dir_prop_selection[3],gd)#(max_var, max_dir, maximum, selected_prop.name)
	  #this needs to be fixed:
    if (mpfr('0') == delta):
    #if (Fraction(0,1) == delta):#was not possible to find a delta (NOTE: ugly, implement using exceptions but need to define a new exception customized for this)
      myprint ("Attempt to nudge into ceg failed inside transform() in this iteration ")
      return final_p
    else:
      gd.delta_obtained = True
      var_dir_prop_selection[0].fp_val+=delta
      myprint("delta that got added is ")
      myprint("{0:.165Df}".format(delta))
      myprint("New value of " +var_dir_prop_selection[0].name+" is "+"{0:.165Df}".format(var_dir_prop_selection[0].fp_val))
      #CR: check the value of the inverted prop by evaluation with library: has it inverted?
      #Check how list of invertinles/maintianables is updated
      bool_result = final_new.evaluate_fp_update(var_dir_prop_selection[0])#update all ArithExp/Prop/PropExp in which this var occurs
      myprint("PropExp is now (bool_result) "+str(bool_result))
      #consistency_check(,23,8)
      if bool_result:
        myprint ("Transform successful, and the WHOLE input formula is satisfied!")
        break
      #else:
      if(inv_prop_val_before == var_dir_prop_selection[3].fp_eval):
        myprint("Error?: selected invertible did not get inverted: result from mathsat, library not adding up inside fit()!")
        print_error_msg(gd, " error?:  selected invertible did not get inverted: result from mathsat and library not adding up inside fit()!\n")
        #CR: add code to find mismatches of vars, arith exps, props, propexps

        #fp = open(gd.summary_filename,"a")
        #fp.write("sat\ntime: "+str(end_time - gd.start_time)+"\n")
        #fp.write("iteration: "+str(iteration)+" with lift\n")
        #fp.write("#####"+gd.input_filename+"#####\n")
        #fp.close()
        #`final_new.fp_eval = True #this is a temporary hack!
        break
      #print gmpy2.get_context()
      final_new.dependency_table(ctx1)#loop around
  return final_new

def transform1(final_p,ctx1,gd):
  myprint("Inside transform1():\nAll props of final_p: ")
  for p in final_p.get_all_props():
      myprint(p.print2())
  final_new = final_p
  all_arith_vars = final_new.get_arith_vars()
  #exit(1)
  delta_dict = final_new.value_change1(gd, all_arith_vars)
  if({} == delta_dict):
    myprint ("Attempt to nudge into ceg failed inside transform() in this iteration ")
    #return final_new
  else:
  #add delta for each var to the var value itself
    for var in all_arith_vars:
      print "Adding for "+var.name+", more specifically, adding "+"{0:.165Df}".format(delta_dict["delta_"+var.name])
      var.fp_val += delta_dict["delta_"+var.name]
  #evaluate and update FP part of each formula
    #bool_result = final_new.evaluate_fp_update(var_dir_prop_selection[0])#update all ArithExp/Prop/PropExp in which this var occurs
    myprint("config used for fp update: "+str(get_context()))
    bool_result = final_new.evaluate_fp_update_all()
    myprint("PropExp is now (bool_result) "+str(bool_result))
  #if evaluates to true say successdful
    if bool_result:
      myprint ("Transform successful, and the WHOLE input formula is satisfied!")
    else:
      myprint("Error?: updated var values do not satisfy formula: result from mathsat, library not adding up inside fit()!")
      print_error_msg(gd, " error?: updated var values do not satisfy formula: result from mathsat and library not adding up inside fit()!\n")
    return final_new

#one variable selected at a time to attempt to invert
def transform2(final_p,ctx1,gd):
  myprint("Inside transform2():\nAll props of final_p: ")
  for p in final_p.get_all_props():
    myprint(p.print2())
  final_new = final_p
  all_arith_vars = final_new.get_arith_vars()
  #exit(1)
  #start a loop that will try one variable at a time, and attempt to make the formula true in one go
  number_vars = len(all_arith_vars)
  for var in all_arith_vars:
    #timeout = str(float(gd.inner_timeout)/float(number_vars))#fixed value of 60 used in FMCAD16 submission
    if (gd.non_symbolic_model_lift):
      myprint("Will import non-symbolic model lift module, and call search_model()")
      from transform_search_based import *
      t1 = time()
      delta_dict = search_model(gd, final_new, var, abs(mpfr('100.0') * var.fp_val)) #CALL NON-SYMBOLIC SEARCH, can change up to 2% of var's current val
      t2 = time()
    else:#Will do symbolic lifting
      timeout = "60"
      #timeout = str(float(gd.inner_timeout)/float(number_vars))#should it be max?
      myprint("Calling value_change2() with variable "+var.name)
      delta_dict = final_new.value_change2(gd, var, number_vars, timeout)
    #The following is common to both symbolic and non-symbolic lifting
    if({} == delta_dict):
      myprint ("Attempt to lift with var " +var.name+" failed inside transform2() in iteration "+str(gd.iteration))
     #myprint ("Attempt to nudge into ceg failed inside transform2() in this iteration ")
      if (gd.non_symbolic_model_lift):
        fstat.write("%.2fsU\t" % (t2 - t1))
      if(not(gd.select_all_vars_in_sequence)):
        return final_new
    else:
    #add delta to the var value itself
      print "Adding for "+var.name+", more specifically, adding "+"{0:.165Df}".format(delta_dict["delta_"+var.name])
      var.fp_val += delta_dict["delta_"+var.name]
    #evaluate and update FP part of formula
    #bool_result = final_new.evaluate_fp_update(var_dir_prop_selection[0])#update all ArithExp/Prop/PropExp in which this var occurs
      myprint("config used for fp update: "+str(get_context()))
      bool_result = final_new.evaluate_fp_update_all()
      myprint("PropExp is now (bool_result) "+str(bool_result))
    #if evaluates to true say successful
      assert(bool_result == final_new.fp_eval)
      if bool_result:
        myprint ("Transform successful, and the WHOLE input formula is satisfied!")
        if (gd.non_symbolic_model_lift):
          fstat.write("%.2fs\t" % (t2 - t1))
        return final_new
      else:
        myprint("Error?: updated var values do not satisfy formula: result from mathsat, library not adding up inside fit()!")
        print_error_msg(gd, " error?: updated var values do not satisfy formula: result from mathsat and library not adding up inside fit()!\n")
  return final_new

#obtain timeout given the number of remaining variables and the remaining time
def get_timeout(gd, vars_rem, time_rem):
  if(1 == vars_rem):
    timeout = time_rem #set aside all remaining time for this variable
  elif(time_rem <= int(gd.tmin_lift)):
    timeout = time_rem #set aside all remaining (small) time for this variable
  elif(2 == vars_rem):
    timeout = 0.6 * float(time_rem)
  elif((0.4 * float(time_rem)) >= int(gd.tmin_lift)):#vars_rem>=3 and rime_rem > gd.tmin_lift
    timeout = 0.4 * float(time_rem)
  else:
    timeout = gd.tmin_lift

  return str(timeout)

#one variable selected at a time to attempt to invert
#each selected variable must occur in a least one invertible
def transform4(final_p,ctx1,gd, time_lift_start):
  ##########
  myprint("Inside transform4():\nAll props of final_p: ")
  #for p in final_p.get_all_props():
  #    myprint(p.print2())
  final_new = final_p
  if(isinstance(final_new,Prop)):
    final_new.categorize_prop()
    myprint("Categorized the only prop remaining as "+final_new.type+ ", error if M or X!")
  else:
    final_new.categorize_props()#as 'I' or 'M'
  inv_arith_vars = []
  invertibles = final_new.invertibles()
  myprint("Invertibles: ")
  for p in  invertibles:
   inv_arith_vars+= p.get_arith_vars()
   myprint(p.print2())
  inv_arith_vars=uniq(inv_arith_vars)
  ###
  all_vars = uniq(final_new.get_arith_vars())
  #inv_arith.sort()
  myprint("Here are only the "+str(len(inv_arith_vars))+" variables occurring in invertibles")
  for var in inv_arith_vars:
    myprint(var.name)
  myprint("Here are ALL the "+str(len(all_vars))+" variables"); m_vars=[]
  for var in all_vars:
    myprint(var.name)
    if not(var in inv_arith_vars):
      m_vars+=[var]
  myprint("m_vars, occur only in maintainables: ")
  for m_var in m_vars:
    myprint(m_var.name)
  #exit(0)
  ###
  maintainables = uniq(final_new.maintainables())
  myprint("Maintainables: ")
  for p in maintainables:
   myprint(p.print2())
  if([]==invertibles):
   msg="Error: empty invertible set I for "+gd.input_filename+" during iteration "+str(gd.iteration)
   myprint(msg)
   fdbg=open(gd.molly_debug_file,"a")
   fdbg.write(msg+"\n")
   fdbg.close()
   if(not gd.abstraction == "approx"):
     return final_new
  ##########
  #start a loop that will try one variable at a time, and attempt to make the formula true in one go
  frank.write("Iteration: "+str(gd.iteration)+"\n")
  if(gd.abstraction  == "approx"):#TEMP CHANGE: check
     inv_arith_vars = all_vars
  number_vars = len(inv_arith_vars)
  ranked_vars = rank(final_new, inv_arith_vars)
  if(gd.reverse_ranked_vars):
    ranked_vars.reverse()
  myprint("Ranked variable list: ")
  for r_var in ranked_vars:
    myprint(r_var.name)
  #sleep(10)
  vars_rem = number_vars
  for var in ranked_vars:
    myprint("var name is: "+var.name)
    #timeout = str(float(gd.inner_timeout)/float(number_vars))#fixed value of 60 used in FMCAD16 submission
    time_rem = int(gd.inner_timeout) - time() + time_lift_start
    timeout = get_timeout(gd, vars_rem, time_rem)
    myprint("Calling value_change2() with timeout of "+str(timeout)+" and variable "+var.name)
    frank.write("Selected variable " + var.name + " for Model Lifting\n")
    # timeout = calculate_timeout(gd, var, number_vars)
    #delta_dict = final_new.value_change2(gd, var, number_vars, timeout) #pass timeout instead of number_vars
    delta_dict = final_new.value_change2(gd, var, number_vars, str(time_rem))
    vars_rem -= 1
    if({} == delta_dict):
      myprint ("Attempt to lift with var " +var.name+" failed inside transform4() in this iteration ")
      if(not(gd.select_all_vars_in_sequence)):
        return final_new
      #myprint("Did not return")
    else:
    #add delta to the var value itself
      print "Adding for "+var.name+", more specifically, adding "+"{0:.165Df}".format(delta_dict["delta_"+var.name])
      var.fp_val += delta_dict["delta_"+var.name]
    #evaluate and update FP part of formula
    #bool_result = final_new.evaluate_fp_update(var_dir_prop_selection[0])#update all ArithExp/Prop/PropExp in which this var occurs
      myprint("config used for fp update: "+str(get_context()))
      bool_result = final_new.evaluate_fp_update_all()
      myprint("PropExp is now (bool_result) "+str(bool_result))
    #if evaluates to true say successdful
      if bool_result:
        myprint ("Transform successful, and the WHOLE input formula is satisfied!")
        return final_new
      else:
        myprint("Error?: updated var values do not satisfy formula: result from mathsat, library not adding up inside fit()!")
        print_error_msg(gd, " error?: updated var values do not satisfy formula: result from mathsat and library not adding up inside fit()!\n")
  myprint ("Attempt to nudge into ceg failed inside transform4() in this iteration ")
  return final_new

def transform5(final_p,ctx1,gd):
  myprint("Inside transform5():\nAll props of final_p: ")
  for p in final_p.get_all_props():
      myprint(p.print2())
  final_new = final_p
  if(isinstance(final_new,Prop)):
    final_new.categorize_prop()
    myprint("Categorized the only prop remaining as "+final_new.type+ ", error if M or X!")
  else:
    final_new.categorize_props()#as 'I' or 'M'
  inv_arith_vars = []
  invertibles = final_new.invertibles()
  myprint("Invertibles: ")
  for p in  invertibles:
   inv_arith_vars+= p.get_arith_vars()
   myprint(p.print2())
  inv_arith_vars=uniq(inv_arith_vars)
  ###
  all_vars = uniq(final_new.get_arith_vars())
  #inv_arith.sort()
  myprint("Here are only the "+str(len(inv_arith_vars))+" variables occurring in invertibles")
  for var in inv_arith_vars:
    myprint(var.name)
  myprint("Here are ALL the "+str(len(all_vars))+" variables"); m_vars=[]
  for var in all_vars:
    myprint(var.name)
    if not(var in inv_arith_vars):
      m_vars+=[var]
  myprint("m_vars, occur only in maintainables: ")
  for m_var in m_vars:
    myprint(m_var.name)
  #exit(0)
  ###
  maintainables = uniq(final_new.maintainables())
  myprint("Maintainables: ")
  for p in maintainables:
   myprint(p.print2())
  if([]==invertibles):
   msg="Error: empty invertible set I for "+gd.input_filename+" during iteration "+str(gd.iteration)
   myprint(msg)
   fdbg=open(gd.molly_debug_file,"a")
   fdbg.write(msg+"\n")
   fdbg.close()
   return final_new

  #all_arith_vars = final_new.get_arith_vars()
  #exit(1)
  delta_dict = final_new.value_change5(gd, inv_arith_vars, m_vars)
  if({} == delta_dict):
    myprint ("Attempt to nudge into ceg failed inside transform5() in this iteration ")
    return final_new
  else:
  #add delta for each var to the var value itself
    for var in inv_arith_vars:
      print "Adding for "+var.name+", more specifically, adding "+"{0:.165Df}".format(delta_dict["delta_"+var.name])
      var.fp_val += delta_dict["delta_"+var.name]
  #evaluate and update FP part of each formula
    #bool_result = final_new.evaluate_fp_update(var_dir_prop_selection[0])#update all ArithExp/Prop/PropExp in which this var occurs
    myprint("config used for fp update: "+str(get_context()))
    bool_result = final_new.evaluate_fp_update_all()
    myprint("PropExp is now (bool_result) "+str(bool_result))
  #if evaluates to true say successdful
    if bool_result:
      myprint ("Transform successful, and the WHOLE input formula is satisfied!")
    else:
      myprint("Error?: updated var values do not satisfy formula: result from mathsat, library not adding up inside fit()!")
      print_error_msg(gd, " error?: updated var values do not satisfy formula: result from mathsat and library not adding up inside fit()!\n")
    return final_new


rounding_modes={'round-to-negative':gmpy2.RoundDown,'round-to-nearest-even':gmpy2.RoundToNearest,'round-to-zero':gmpy2.RoundToZero,'round-to-positive':gmpy2.RoundUp,'round-to-nearest-away':gmpy2.RoundAwayZero}

def get_precision(cfg):
  return int(cfg[0].rstrip("\n"))+1

def get_rnd_mode(cfg):
  return rounding_modes[cfg[1].rstrip("\n")]

# The following function returns a pair (result, assignment)
# assignment[var.name] is an mpq value (Rational), read from
# the proxy solver's output. For RPFPA, it is the (s,e,m) OR
# unsigned integer output converted to Rational
def proxy_smt_solver(constraint, pexp, gd, iteration):#CFR
  result,assignment = ("Failed",None)
  input_file_name_split = gd.input_filename.split("/")
  constraint_filename="smt2_files/"+input_file_name_split[len(input_file_name_split) - 1].rstrip(".fml").rstrip(".smt2")+"_iter_"+str(iteration)+".smt2"
  #constraint_filename = "lfp-constraint.smt2"
  f2 = open(constraint_filename,"w")
  f2.write(constraint)
  f2.close()
  temp_filename = "smt2_files/iter1_constants2.smt2"
  #myprint("Exiting from within proxy_smt_solver");#exit(0)
  try:
    myprint("Calling Proxy solver (mathsat/z3) now on low precision FPA/RA formula: ")
    myprint(ctime())
    t1=time()
    force_lower_to = False
    #to_str=" "
    if(True):#('Linux'==platform.system()):
     time_left = float(gd.overall_timeout) - float(t1 - gd.start_time)
     if time_left < 0:
       myprint("Overall timeout exceeded before outer loop in iteration "+str(gd.iteration))
       print_final(gd)#TODO:enhance to stats printing
     if(time_left < float(gd.outer_timeout)):
      to = str(time_left)
      force_lower_to = True
      #to_str = "T"
     else:
      to = gd.outer_timeout

     if(gd.abstraction == "lfp"):
       output2 = subprocess.check_output(('timeout',to,'mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=1','-theory.fp.bit_blast_mode=1' ,'-model',constraint_filename), stderr=subprocess.STDOUT)
     elif (gd.abstraction == "real"):
       output2 = subprocess.check_output(('timeout',to,'z3','-st','dump_models=true','-smt2',constraint_filename), stderr=subprocess.STDOUT)
       #myprint("Raw output of z3: "+output2); exit(0)
     else:#gd.abtsraction = "approx"
       myprint(constraint)
       #myprint("Printed dReal constraint and exiting")
       output2 = subprocess.check_output(('time','timeout','1200','dReal','--model','--precision','0.001',constraint_filename), stderr=subprocess.STDOUT)
       #exit(0)
      #else:#non-linux systems might not have timeout command: check for a fix later
    # output2 = subprocess.check_output(('mathsat','-input=smt2','-theory.eq_propagation=false','-printer.fp_number_format=1','-theory.fp.bit_blast_mode=1' ,'-model',constraint_filename), stderr=subprocess.STDOUT)
    t2=time()
    #fstat.write("%.2fs\t" % (t2 - t1))
    myprint(ctime())
    print pexp.name
    #var_obj_list = pexp.get_arith_vars()
    #print(len(var_obj_list))
    #print(var_obj_list)
    if(gd.enable_abstract_check):
      #a=10
      obj_list = gd.ordered.keys()
    else:
      obj_list = pexp.get_arith_vars()
    var_list = []
    for var in obj_list:
      var_list += [var.name]
    print pexp.preorder()
    print var_list
    #myprint("PPP: "+output2+"\nPPP")
    if(gd.abstraction == "lfp"):
      assignment = parse_mathsat_output(output2,var_list,"sme",gd)
    elif(gd.abstraction == "real"):
      if("unsat"==output2[0:5]):
        result = "Unsat"
        #fstat.write("%.2fsN\t" % (t2 - t1))
        assignment = None
      assignment = parse_solver_output(output2,var_list, "z3")
    else:#gd.abstraction = "approx"
      if("unsat" == output2[0:5]):
        result = "Unsat"
        assignment = None
      myprint(output2)
      myprint("Printed dReal output and exiting")
      assignment = parse_solver_output(output2, var_list, "dreal")
      #exit(0)
    #myprint(assignment)
    if None == assignment:
     result = "Unsat"
     fstat.write("%.2fsN\t" % (t2 - t1))
    elif "error" == assignment:
     t2=time()
     fstat.write("%.2fsE\t---" % (t2 - t1))
     myprint("mathsat error on low precision formula call")
     result, assignment = ("Failed", None)
    else:
     result = "Sat"
     fstat.write("%.2fs\t" % (t2 - t1))
  except subprocess.CalledProcessError:
     t2=time()
     if(force_lower_to):
      fstat.write("%.2fsT\t---" % time_left)
      print_final(gd)
     else:
      fstat.write("%.2fst\t---" % (t2 - t1))
     myprint("subprocess.calledProcessError!")
     result, assignment = ("Failed", None)
  except MyError as e:
     myprint("Exiting due to error");exit(1)
     t2=time()
     fstat.write("%.2fsE\t---" % (t2 - t1))
     myprint(e)
     result, assignment = ("Failed", None)
  fstat.flush()
  os.fsync(fstat)
  return (result,assignment)

def real_smt_solver(constraint):
  f1 = open(ARITH_VARS_FILE,"r")
  var_list = f1.readline().rstrip(" ").lstrip(" ").split(" ")
  f1.close()
  f2 = open("z3-mixed-constraint.smt2","w")
  f2.write(constraint)
  f2.close()
  #ps2 = subprocess.Popen(('echo',constraint),stdout=subprocess.PIPE)
  try:
    myprint("Calling z3 now on Mixed (Real) formula: ")
    myprint(ctime())
    t1=time()
    output2 = subprocess.check_output(('z3','-st','dump_models=true','-smt2','-T:'+str(Z3_MIXED_TIMEOUT),'z3-mixed-constraint.smt2'),stderr=subprocess.STDOUT)
    t2=time()
    #fstat.write("%.2fs\t" % (t2 - t1))
    myprint(ctime())
    if("unsat"==output2[0:5]):
      result = "Unsat"
      fstat.write("%.2fsN\t" % (t2 - t1))
      assignment = None
    else:
      assignment = parse_solver_output(output2,var_list)
    #if(Fraction('0') == assignment['delta']):
    # result = "Timeout"
      result = "Sat"
      fstat.write("%.2fs\t" % (t2 - t1))
  except subprocess.CalledProcessError:#can happen if constraint is UNSAT and we have (get-model) in the z3 constraint
     t2=time()
     fstat.write("%.2fsE\t---" % (t2 - t1))
     myprint("subprocess.calledProcessError!")
     result, assignment = ("Failed", None)
  except MyError as e:
     t2=time()
     fstat.write("%.2fsE\t---" % (t2 - t1))
     myprint(e)
     result, assignment = ("Failed", None)
  fstat.flush()
  os.fsync(fstat)
  return (result,assignment)

def generate_real_but_not_fp_smt2(formula):
  #call translator on (not formula)
  formula=formula.rstrip("\n")
  negated_formula = "(not "+formula+")"
  myprint(negated_formula)
  ps = subprocess.Popen(('echo', negated_formula), stdout=subprocess.PIPE)
  global TRANSLATOR_CFG_FP
  output = subprocess.check_output((TRANSLATOR_PATH,TRANSLATOR_CFG_FP,'var-list.txt'), stdin=ps.stdout)#USE appropriate CONFIG file acc to PRECISION/RANGE
  ps.wait()
  #print "Translator-expts o/p: "+output
  output = output.replace("(check-sat)\n(get-model)","")
  #strip (check-sat) (get-model)
  #append formula
  output+="\n(assert "+formula.rstrip("\n")+")\n"
  #append check-sat get-model
  output+="\n(check-sat)\n(get-model)"
  #print output
  return output

def compare_solver_code_values():
 #check dictionaries type wise
 return

def set_fpa(prec, exp, rnd_mode=RoundToNearest):
  ctx = get_context()
  ctx.precision = prec
  ctx.round = rnd_mode
  ctx.emax = 2**(exp - 1); ctx.emin = 4 - ctx.emax - ctx.precision; ctx.subnormalize = True
  #ctx.emax = 2**(exp - 1) - 1; ctx.emin = - (ctx.emax + 1)
  set_context(ctx)


def assign_abstract_val_consts(gd):
  set_fpa(gd.precision + 1, gd.exponent, RoundDown)
  for const in gd.consts.keys():
    if(gd.abstraction=="lfp"):
      gd.consts[const].abstract_val = mpfr(gd.consts[const].original_val)
      gd.consts[const].abstract_solver_val = mpfr('0')
    else:
      gd.consts[const].abstract_val = gd.consts[const].original_val
      gd.consts[const].abstract_solver_val = Fraction(0,1)

  set_context(ieee(32))
   #gd.consts[const].fp_solver_val = mpfr('0')#should be full prec val

#the top-level function in the paper
def main(arg_dict,gd):
  global fassn
  #sys.setrecursionlimit(2500)
  if(arg_dict['smt2']!=None):
    gd.input_filename = arg_dict['smt2']
  elif(arg_dict['fml']!=None):
    gd.input_filename = arg_dict['fml']
  
  frank.write("\n###"+ gd.input_filename+"\n")
  #print len(argv)
  initialize_summary_file(gd,gd.input_filename)
  fstat.write("\n"+gd.input_filename)
  fstat.flush()
  os.fsync(fstat)
  formula_file = open(gd.input_filename,"r")
  formula = formula_file.readline()
  formula_file.close()
  if(arg_dict['abstraction']=="lfp"):
    gd.abstraction = "lfp"
    saved_abs = "lfp"
  elif(arg_dict['abstraction']=="real"): #abstraction is Real
    gd.abstraction="real"
    saved_abs = "real" # could be "real" or "lfp"
  elif(arg_dict['abstraction'] == "approx"):
    gd.abstraction="approx"
    saved_abs = "approx" # could be "real" or "lfp"
  else:
    myprint("Error: Abstraction not supplied")
    exit(1)
  iteration = 1
  #CR: remove the real abstr conditional, re-use parts for lfp abstraction for .fml,.cfg format as reqd
  if (None!=arg_dict['fml']):#("real" == gd.abstraction):
   #Read the two command-line arguments to program. <>.fml, <>.cfg
   global TRANSLATOR_CFG_FP
   TRANSLATOR_CFG_FP = arg_dict['cfg']
   cfg_file = open(arg_dict['cfg'],"r")
   cfg = cfg_file.readlines()
   myprint(cfg)
   cfg_file.close()
   cfg_mixed = cfg[0].rstrip("\n")+"\n"+cfg[1].rstrip("\n")+"\n"+cfg[2].rstrip("\n")+"\n"+cfg[3].rstrip("\n")+"\n"+cfg[4].rstrip("\n")+"\n"+cfg[5].rstrip("\n")+"\n"+cfg[6].rstrip("\n")+"\n"+"mixed\n"
   global TRANSLATOR_CFG_MIXED
   TRANSLATOR_CFG_MIXED = TRANSLATOR_CFG_FP.rstrip(".cfg")+"-mixed.cfg"
   #print "MIXED CFG: " +TRANSLATOR_CFG_MIXED
   cfg_mixed_file = open(TRANSLATOR_CFG_MIXED,"w")
   cfg_mixed_file.write(cfg_mixed)
   cfg_mixed_file.close()
   #set the gmpy2 context (precision, rounding mode)
   ctx = gmpy2.get_context()
   ctx1 = set_prec_mode(get_precision(cfg), get_rnd_mode(cfg), ctx)
   #generate code to create and initialize data structures
   ps2 = subprocess.Popen(('echo', formula), stdout=subprocess.PIPE)
   input_filename = gd.input_filename

   try:
    myprint("Calling parser-generator now: ")
    output2 = subprocess.check_output((PARSER_GENERATOR_PATH,arg_dict['cfg'],ARITH_VARS_FILE), stdin=ps2.stdout,stderr=subprocess.STDOUT)
    from initialize2 import *#parser generator above outputs parser code in ``initialize2.py''
   except subprocess.CalledProcessError:
    myprint("ERROR: call to parser-generator failed")
    end_time = time()
    fp = open(gd.summary_filename,"a")
    fp.write("error\ntime: "+str(end_time - gd.start_time)+"\n")
    fp.write("iteration: "+str(iteration)+"\nparser-generator call\n")
    #fp.write("#####"+gd.input_filename+"#####\n")
    fp.close()
    exit(1)
   myprint("Import successful")
   gd.input_filename = input_filename
  else:# in .smt2 format
   # call parse.py
   #ps2 = subprocess.Popen(('echo', formula), stdout=subprocess.PIPE)
   #CR: can this be made into an internal function instead of the convoluted external call + import ?
   try:
    myprint("Calling bv_parser-generator now: ")
    #myprint()
    output2 = subprocess.check_output((BV_PARSER_GENERATOR_PATH,gd.input_filename), stderr=subprocess.STDOUT)#fix reqd to handle Boolean constants in .smt2 file
   except subprocess.CalledProcessError:
    fp = open(gd.summary_filename,"a")
    end_time = time()
    fp.write("error\ntime: "+str(end_time - gd.start_time)+"\n")
    fp.write("iteration: "+str(iteration)+"\nparser-generator call failed\n")
    #fp.write("#####"+gd.input_filename+"#####\n")
    fp.close()
    myprint("ERROR: call to bv_parser-generator failed")
    exit(1)
   #print output2
   input_filename = gd.input_filename
   parser_output_file = open('parser_output.py','w')
   parser_output_file.write(output2)
   parser_output_file.close()
   #myprint("Only TESTING gd!")
   #gd.consts['testcons'] = 'testcons-value'
   #myprint(gd.consts['testcons'])
   #CR: check if there is a way to avoid this; namespace; is GlobalData or other unintended data being overridden?
   from  parser_output import *#parser generator above outputs parser code in ``parser_output.py''
   gd.input_filename = input_filename
   #myprint(gd.ordered)
   #myprint("Size of gd.ordered = "+str(len(gd.ordered)))
   for key in gd.ordered.keys():
     myprint(key.print_one_smtlib_stmt(gd))
   myprint("Import successful")
   #exit(0)

  myprint("Constants Abstract:")
  for const_name in gd.consts.keys():
    if(gd.abstraction=="lfp"):
      myprint(const_name+": "+"{0:.10Df}".format(gd.consts[const_name].abstract_val,precision=4,emax=4,emin=-4,subnormalize=True)+" Mathsat: "+"{0:.10Df}".format(gd.consts[const_name].abstract_solver_val))
    else:
      myprint(const_name)
      print gd.consts[const_name].abstract_val
      myprint(" RA/approx solver: ")
      print gd.consts[const_name].abstract_solver_val

  gd.abstraction = saved_abs #restoring the overwritten value # clean-up reqd
  iteration = 1#count for top-level loop
  myprint("######################################\n")
  #myprint(propexp.named_prefix())
  #####
  myprint("PRINTING DEGREES OF VARS IN THE PROPEXP")
  for var in propexp.get_arith_vars():
    myprint("Degree of "+var.name+" in propexp is "+str(propexp.deg(var)))
  #exit(0)
  #####
  myprint("Starting with iterations now, abstraction is "+gd.abstraction)
  myprint("######################################\n")
  while True:#loops as long as there is scope for refinement and sat assign not found
   if((iteration >= 2) and (not (gd.abstraction =="lfp"))):#: currently don't support refinement for real arith abstraction
    myprint("End of first iteration using "+gd.abstraction+" abstraction, exiting")
    exit(0)#break out of the refinement while loop

   is_unsat = False
   gd.iteration = iteration
   fstat.write("\nIteration "+str(iteration)+"\n")
   fstat.flush()
   os.fsync(fstat)
    #if(5 == iteration):
    #  print "Iteration 5 reached, exiting!!"
    #  exit(1)
   #CR: remove real abstraction
   myprint("CHECK: "+gd.abstraction)

   assign_abstract_val_consts(gd)  #get/assign the appropriate abstract value for the constant values in the input formula

   #print gd.avars
   #print gd.consts; exit(1)
   if(0):
    iteration = iteration
   else:
    if(gd.generate_benchmark):
      gd.exponent = 8
      gd.precision = 23
      constraint = gd.generate_smtlib_fp()+"(assert propexp)\n(check-sat)\n"
      if(not gd.generate_benchmark_dreal):
        constraint+="(get-model)\n"
      constraint+="(exit)"
      print constraint
      part = gd.input_filename.split("/")
      benchmark_filename = part[len(part)-1]
      print(benchmark_filename)
      if(-1 != benchmark_filename.find("fml")):
        benchmark_filename = benchmark_filename.rstrip("fml")+"smt2"
        #exit(0)
      #exit(0)
      # Write the constraint being solved, into a file
      if(gd.generate_benchmark_real):
        rel_bm_dir = "examples/polynomials/smt2/for-numerical/z3/"#"misc/benchmarks/converted/"#examples/polynomials
      elif(gd.generate_benchmark_dreal):
        rel_bm_dir = "examples/polynomials/smt2/for-numerical/dreal/"#"misc/benchmarks/converted/"#examples/polynomials
      else:
        #myprint("Directory to generate benchmarks not set. Also, which Theory?")
        myprint("Assuming you need becnhmarks written in FPA")
        rel_bm_dir = "examples/polynomials/smt2/fpa/"#"misc/benchmarks/converted/"#examples/polynomials
        rel_bm_dir = "misc/benchmarks/converted/false-identity/"#"misc/benchmarks/converted/"#examples/polynomials
        
        #exit(1)
      #fpb = open(rel_bm_dir+benchmark_filename,"w")
      fpb = open(rel_bm_dir+benchmark_filename,"w")#("smt2_files/"+benchmark_filename,"w")
      fpb.write(constraint)
      fpb.close()
      #print constraint
      #print "examples/polynomials/"+benchmark_filename
      myprint("Exiting after generating benchmark in the required format in "+rel_bm_dir)
      exit(0)
    constraint = ""
    #if(gd.generate_benchmark_dreal):
    #  constraint += "(set-logic QF_NRA)"
    constraint += gd.generate_smtlib_fp()+"(assert propexp)\n(check-sat)\n"
    if(gd.enable_abstract_check and (not (gd.abstraction=="real"))):#CFR: z3 parsing check!
     constraint+="(get-value ("
     for obj in gd.ordered.keys():
      constraint+=obj.name+" "
     constraint = constraint.rstrip(" ")
     constraint+="))\n"
    constraint+="(exit)"
    myprint("Iteration: "+str(iteration)+ ", converted to lfp constraint")
    #Following line is the SMT call to the converted lfp constraint
    #myprint(constraint)
    result, assignment = proxy_smt_solver(constraint, propexp, gd, iteration) #mathsat on above constraint (system call)
    myprint("Returned from smt solver sat call (top-level algo), result : "+result)
    #exit(0)
   #COMMON PART for both abstractions: sat/unsat result and approx assignment obtained
   #myprint(assignment)
   #myprint("Exiting main loop after call to low prec")
   #exit(1)
   myprint("Constants Abstract in main() after return from proxy_smt_solver():")
   for const_name in gd.consts.keys():
    if(gd.abstraction == "lfp"):
      myprint(const_name+": "+"{0:.10Df}".format(gd.consts[const_name].abstract_val,precision=4,emax=4,emin=-4,subnormalize=True)+" Mathsat: "+"{0:.10Df}".format(gd.consts[const_name].abstract_solver_val))
    else:
      myprint(const_name+": ")
      print gd.consts[const_name].abstract_val
      myprint(" z3 : ")
      print gd.consts[const_name].abstract_solver_val

   if("Unsat" == result):
     is_unsat = True
   elif("Sat" == result):# satisfying assignment was found for the approximation
    #Assign and Floatify
    for var in propexp.get_arith_vars():
       if(gd.abstraction == "lfp"):
       #GET ABSTRACT VALUE
         ctx = get_context()
         ctx.precision = gd.precision + 1; ctx.emax = 2**(gd.exponent - 1); ctx.emin = 4 - ctx.emax - ctx.precision; ctx.subnormalize = True #also change emax and emin
         set_context(ctx)
       #print get_context()#should be that for reduced precision FP, incl emax, emin
         var.abstract_val = mpfr(assignment[var.name])#real value#CFR: retain the assignment as is for RA proxy, no need to call mpfr()
       else:
         print "Assignment"
         print assignment
         print var.name
         var.abstract_val = assignment[var.name]#real value#CFR: retain the assignment as is for RA proxy, no need to call mpfr()
         assert isinstance(var.abstract_val,Fraction)
       #GET FULL FP VALUE
       #TODO: write a function that sets to problem's FP settings, optimize
       # do set_context(ieee(32)) instead of below 3 lines
       ctx = get_context()
       ctx.precision = 24; ctx.emax = 128; ctx.emin = 4 - ctx.emax - ctx.precision; ctx.subnormalize = True #also change emax and emin
       set_context(ctx)
       var.fp_val = mpfr(var.abstract_val)#floatifies the value#CFR: no change?
       #print get_context()
       #exit(1)
       if(gd.abstraction == "lfp" and (var.abstract_val != var.fp_val)):
         myprint("Floatify(): variable "+var.name+ " actually needed to be rounded for FPA! Iteration: "+str(iteration))
    if(gd.enable_abstract_check and gd.abstraction == "lfp"):#not yet implemented for "real" or "approx"
      for obj in gd.ordered.keys():
        if(isinstance(obj,Var) or isinstance(obj,Const) or isinstance(obj,ArithExp)):
          ctx = get_context() #save context
          set_fpa(gd.precision + 1, gd.exponent) #set acc. to current precision
          obj.abstract_solver_val = mpfr(assignment[obj.name])
          set_context(ctx) #revert to the saved context
        elif(isinstance(obj,Prop) or isinstance(obj,PropExp)):
          obj.abstract_solver_eval = assignment[obj.name] # will be true or false
        else:
          myprint("Obj is not any of Var, Const, ArithExp, Prop, PropExp")

    for var in propexp.get_arith_vars():
     if(gd.abstraction == "real" or gd.abstraction == "approx"):
       assert (isinstance(var.abstract_val, Fraction))
     myprint("Abstract "+ var.name +": "+str(var.abstract_val)+"; FP "+var.name+": "+"{0:.165Df}".format(var.fp_val))
     #real_sat = propexp.evaluate_mixed_update_all()#updates all arith exps, prop, propexp based on re-evaluation: real interp
     #Moved following call here from below:
     #abstract_sat = propexp.evaluate_mixed_update_all()
    #CR: remove real
    if(0):
     is_unsat = is_unsat
    else:
     ctx = gmpy2.get_context()
     ctx1 = set_prec_mode(24,gmpy2.RoundToNearest,ctx)
     ctx1.emax = 128
     ctx1.emin = -148
     #do set_context(ieee(32)) instead of above
    myprint("config used for fp update: "+str(get_context()))
    float_sat = propexp.evaluate_fp_update_all()#updates all arith exps, prop, propexp based on re-evaluation: float interp
    #This is important: abstract_sat use mixed semantics!, to get ideal values for all props: This does n't change for this loop
    #remove real
    if(0):
     is_unsat = is_unsat
    elif(gd.abstraction == "lfp"):#lfp abstraction
     ctx_check = get_context()
     ctx1 = set_prec_mode(gd.precision+1,gmpy2.RoundToNearest,ctx_check)#ignoring the lower value of exponent, since it is only used for evaluation: is this ok?
     ctx1.emax = 2**(gd.exponent - 1) # - 1 its just a power of two
     ctx1.emin  =  4 - ctx1.emax - gd.precision -1 #old -ctx1.emax -1
     myprint("config used for low prec eval: "+str(get_context()))
    abstract_sat = propexp.evaluate_prec_update_all()#CFR: this function should operate with Rational (mpq) for RA proxy

    #####DEBUG CODE###
    print get_context()
    myprint("ArithExps Abstract:")
    for aexp in propexp.get_all_arithexps():
      if(gd.abstraction == "lfp"):
        print aexp.abstract_val
        print aexp.abstract_solver_val
        myprint(aexp.name + ": {0:.10Df}".format(aexp.abstract_val)+" Mathsat: "+"{0:.10Df}".format(aexp.abstract_solver_val))
      else:
        myprint(aexp.name)
        print type(aexp.abstract_val)
        assert (isinstance(aexp.abstract_val,Fraction))
        #assert (isinstance(aexp.abstract_solver_val,Fraction))
        myprint(aexp.name + ": ")
        print aexp.abstract_val
        myprint(" RA value: ")
        print aexp.abstract_solver_val
    #myprint("lit_49: "+"{0:.10Df}".format(gd.consts['lit_49'].abstract_val))
    #exit(1)
    #print all constants
    #set_fpa(4,3)
    #exit(0)

    myprint("Constants Abstract:")
    #for const_name in gd.consts.keys():
    # myprint(const_name+": "+"{0:.10Df}".format(gd.consts[const_name].abstract_val,precision=4,emax=4,emin=-4,subnormalize=True)+" Mathsat: "+"{0:.10Df}".format(gd.consts[const_name].abstract_solver_val))
    #myprint("Vars Abstract:")
    #for avar in propexp.get_arith_vars():
    # myprint(avar.name+": "+"{0:.10Df}".format(avar.abstract_val)+" Mathsat: "+"{0:.10Df}".format(avar.abstract_solver_val))
    #myprint("lit_62: "+"{0:.10Df}".format(gd.arithexps['lit_62'].abstract_val))
    #exit(1)
    ######END DEBUG CODE#######

    myprint("comment the following too:")
    #myprint("Debug values: ")
    #myprint(Fraction(str(propexp.left_exp.rel_exp.left.fp_val)))#only if propexp is a conjunction with no others structure
    #myprint(Fraction(str(propexp.left_exp.rel_exp.right.fp_val)))
    #myprint("abstract_sat = "+ str(abstract_sat))i
    #CR: there should be no mixed one here as it is all RP, no reals: rename it to RP!

    if(isinstance(propexp,PropExp)):# is a PropExp
      propexp.print_all_props()
      #for p in propexp.get_all_props():
      #  myprint(p.rel_exp.left.name+ " :: FP: "+"{0:.165Df}".format(p.rel_exp.left.fp_val)+ " Abstract: "+str(p.rel_exp.left.abstract_val))
      #  myprint(p.rel_exp.right.name+ " :: FP: "+"{0:.165Df}".format(p.rel_exp.right.fp_val)+ " Abstract: "+str(p.rel_exp.right.abstract_val))
        #myprint("{0:.165Df}".format(p.rel_exp.left.fp_val))
        #myprint(p.rel_exp.left.abstract_val)
        #myprint(p.rel_exp.right.abstract_val)
    else:#it is a Prop
      propexp.print_prop()
      #myprint("{0:.165Df}".format(propexp.rel_exp.left.fp_val))
      myprint("{0:.165Df}".format(propexp.rel_exp.left.abstract_val))
      myprint("{0:.165Df}".format(propexp.rel_exp.right.fp_val))
      #myprint("{0:.165Df}".format(propexp.rel_exp.right.abstract_val))
    #exit(1)
    myprint("abstract_sat is "+str(abstract_sat))
    myprint("float_sat is "+str(float_sat))
    #exit(0)
    #CR: add a function to check where abstract (called mixed here) don't match
    if(gd.enable_abstract_check and (not (gd.abstraction == "approx"))):
      check_abstract_values_pylib_solver(propexp,gd)#compares gmpy2 value (abstract_val) with SMT solver's value (abstract_solver_val) for every SMT-LIB var
    #compare_abstract_float()
    #CR: add a block to call out to mathsat/z3 and check individual values here
    #compare_solver_code_values()
    #ctx = gmpy2.get_context()
    #set_prec_mode(24,gmpy2.RoundToNearest,ctx_check)
    if(not abstract_sat and (not (gd.abstraction == "approx"))):
      myprint("Error: purported (approx) assignment does not satisfy abstract formula")
      print_error_msg(gd," error, iteration "+str(iteration)+": purported (approx) assignment does not satisfy abstract formula\n")
      if(gd.enable_strict_consis_check):
       exit(1)
    if float_sat:
       end_time = time()
       fp = open(gd.summary_filename,"a")
       fp.write("sat\ntime: "+str(end_time - gd.start_time)+"\n")
       fp.write("iteration: "+str(iteration)+" without lift\n")
       #fp.write("#####"+gd.input_filename+"#####\n")
       fp.close()
       #CR: final SAT assignment should be checked with mathsat/z3
       consistent = True
       if(gd.enable_final_fp_check):
         old_abs = gd.abstraction #save abstraction, will be restored after check
         old_generate_benchmark_real = gd.generate_benchmark_real #save this parameter value
         gd.abstraction = 'lfp'
         gd.generate_benchmark_real = False
         consistent = check_fp_values_pylib_solver(propexp, gd)
         gd.abstraction = old_abs #restore abstraction value
         gd.generate_benchmark_real = old_generate_benchmark_real #restore
         gd.checking_phase = False
       if(not consistent):
         myprint("check_fp indicates not satisfying!")
       myprint("Formula satisfiable in iteration "+str(iteration)+ " w/o needing fit().\nTHE SATISFYING FP ASSIGNMENT IS: ")
       for var in propexp.get_arith_vars():
         #print var.name + ": "+str(var.fp_val)
         myprint (var.name + " = "+"{0:.165Df}".format(var.fp_val) )
         fassn.write("\n(assert (= "+ var.name+ " "+"{0:.165Df}".format(var.fp_val)+"))")
         fassn.flush()
         os.fsync(fassn)
       fassn.close()
       exit(0)
    else:# (not float_sat) is true
      if gd.no_lifting:#dummy if
        myprint("Assignment does not satisfy formula using FP semantics, will refine without attempting to lift")
        propexp.categorize_props()
      else:#
        myprint("Assignment does not satisfy formula using FP semantics, will call the Model Lifting procedure transform()")
        fpl = open(gd.lift_app,"a")
        fpl.write("Lifting applicable on "+gd.input_filename+"\n")
        fpl.write("#####"+gd.input_filename+"#####\n")
        fpl.close()
        #exit(0)
        consistent = True
        old_abs = gd.abstraction
        old_generate_benchmark_real = gd.generate_benchmark_real
        gd.abstraction = 'lfp'
        gd.generate_benchmark_real = False
        consistent = check_fp_values_pylib_solver(propexp, gd)
        gd.abstraction = old_abs
        gd.generate_benchmark_real = old_generate_benchmark_real
        gd.checking_phase = False
        if(not consistent):
          myprint("check_fp indicates satisfying!")
        #propexp.categorize_props()
        #ctx = gmpy2.get_context()
        #ctx1 = set_prec_mode(24,gmpy2.RoundToNearest,ctx)
        #ctx1.emax = 127
        #ctx1.emin = -128
        myprint(get_context())
        myprint("Context just before transform()")
        #call appropriate transform<n>, depending on the policy

        if(0 == gd.var_selection_policy):
          propexp = transform0(propexp,ctx1,gd)#attempt to
        elif(1 == gd.var_selection_policy):
          propexp = transform1(propexp,ctx1,gd)#attempt to
        elif(2 == gd.var_selection_policy):
          propexp = transform2(propexp,ctx1,gd)#attempt to
        elif(4 == gd.var_selection_policy):
          time_lift = time()
          propexp = transform4(propexp,ctx1,gd, time_lift)#attempt to
        elif(5 == gd.var_selection_policy):
          propexp = transform5(propexp,ctx1,gd)#attempt to
        else:
          print "Not yet implemented"; exit(0)
        if(isinstance(propexp,PropExp)):
          propexp.print_all_props()
        else:
          propexp.print_prop()
        if propexp.fp_eval:
          end_time = time()
          fp = open(gd.summary_filename,"a")
          fp.write("sat\ntime: "+str(end_time - gd.start_time)+"\n")
          fp.write("iteration: "+str(iteration)+" with lift\n")
          fp.write("#####"+gd.input_filename+"#####\n")
          fp.close()
          #CR: final SAT assignment should be checked with mathsat/z3
          consistent = True
          consistent = check_fp_values_pylib_solver(propexp, gd)
          gd.checking_phase = False
          if(not consistent):
            myprint("check_fp indicates not satisfying!")
          myprint("Formula satisfiable in FP in iteration "+str(iteration)+ " after fit().\nTHE SATISFYING FP ASSIGNMENT IS: ")
          for var in propexp.get_arith_vars():
          #print var.name + ": "+str(var.fp_val)
           myprint(var.name + " = " +"{0:.165Df}".format(var.fp_val))
           fassn.write("\n(assert (= "+ var.name+ " "+"{0:.165Df}".format(var.fp_val)+"))")
          fassn.flush()
          os.fsync(fassn)
          fassn.close()
          exit(0)
        if isinstance(propexp,Prop):#construct a PropExp instance yet again
         const_1 = Const(mpfr(Fraction('1')),Fraction('1'),gd,'const_1')
         const_2 = Const(mpfr(Fraction('2')),Fraction('2'),gd,'const_2')
         relexp_1 = RelExp(const_1,'<',const_2)
         prop_1 = Prop('prop_1',relexp_1,gd)
         propexp = PropExp(gd, 'propexp',propexp,'and',prop_1)
   else:#UNSAT or failed for some reason, the approximation was unsatisfiable
     myprint("Since the result was not SAT, we will just refine for now")
     #is_unsat = True# could have been TIMEOUT or UNKNOWN too
     #exit(0)
   if(propexp.refine(is_unsat,gd)):#unstable refine for lower precision FP removed
    myprint("Refinement failed in iteration "+str(iteration))
    if(is_unsat):# will is_unsat be set if outer loop sat call had failed due to some other reason (i.e. non necessarily UNSAT)
      end_time = time()
      fp = open(gd.summary_filename,"a")
      fp.write("unsat\ntime: "+str(end_time - gd.start_time)+"\n")
      fp.write("iteration: "+str(iteration)+"\n")#should be the max iteration!
      #fp.write("#####"+gd.input_filename+"#####\n")
      fp.close()
      myprint ("Formula is UNSAT")
      exit(0)
    break#out of the while loop
   iteration = iteration + 1
   gd.iteration = iteration
  #end of while loop

  #Refine() has failed
  #if(the last top-level smt solver call was unsat and refine() failed):
     #the formula is actually unsat
  #else:
     #call realizer with .fml, .cfg (system calls: cat | translator | z3 | pprint)
  #flog.close()

def demo_code():
  return ""#emptied for now

def initialize_summary_file(gd,input_filename):
 #gd.input_filename = input_filename
 fp = open(gd.summary_filename,"a")
 fp.write("#####"+input_filename+"#####\n")
 fp.close()

def write_file_for_parser(args):
  d = vars(args)
  f1= open("molly.opt","w")
  for k in d.keys():
    f1.write(str(k)+"|"+str(d[k])+"\n")
  f1.close()

myprint(STATFILE)
fstat=open(STATFILE,"a")
frank=open(RANKFILE,"a")
if __name__ == "__main__":

 gd = GlobalData()
 parser = argparse.ArgumentParser()
 parser.add_argument("-a","--abstraction", help="proxy theory: real or lfp", default="lfp")
 parser.add_argument("-smt2","--smt2", help="path to smt2 input formula file", default=None)
 parser.add_argument("-fml","--fml", help="path to input formula file in fully parenthesized prefix form", default=None)
 parser.add_argument("-cfg","--cfg", help="path to input config file", default=None)
 parser.add_argument("-edb","--enable_delta_bounds", help="delta bound for model lifting", action="store_true", default=False)
 parser.add_argument("-vsp","--var_selection_policy", help="variable selection policy", type=int, choices= [0,1,2,4,5], default=2)
 parser.add_argument("-gb","--generate_benchmark", help="write out the input formula in SMT2 and exit", action="store_true", default=False)
 parser.add_argument("-gbr","--generate_benchmark_real", help="generate formula in the SMT-LIB format of QF_NRA for z3", action="store_true", default=False)
 parser.add_argument("-gbd","--generate_benchmark_dreal", help="generate formula in the input language of dReal", action="store_true", default=False)
 parser.add_argument("-toa","--try_own_assignment", help="supply own assignment instead of solving proxy formula", action="store_true", default=False)
 parser.add_argument("-nsml","--non_symbolic_model_lift", help="model lifting by local search", action="store_true", default=False)
 parser.add_argument("-lsef","--local_search_exp_factor", help="the exponential factor used in local search to control range for search", type=str, default='2')
 parser.add_argument("-mdbf","--molly_debug_file", help="the debug file name", type=str, default="molly_debug.txt")
 parser.add_argument("-ovt","--overall_timeout", help="Timeout (in seconds) for MOLLY as a whole", type=str, default="12")
 parser.add_argument("-ot","--outer_timeout", help="outer loop solver timeout", type=str, default="180")
 parser.add_argument("-it","--inner_timeout", help="inner loop solver timeout", type=str, default="60")
 parser.add_argument("-tml","--tmin_lift", help="", type=str, default="10")
 parser.add_argument("-eac","--enable_abstract_check", help="", type=str,
     choices=["True", "true", "False", "false"], default="False")
 parser.add_argument("-effc","--enable_final_fp_check", help="", type=str,
     choices=["True", "true", "False", "false"], default="False")
 parser.add_argument("-escc","--enable_strict_consis_check", help="", type=str,
     choices=["True", "true", "False", "false"], default="False")
 parser.add_argument("-eon","--enable_only_normal", help="abc", type=str, choices=["True", "true", "False", "false"], default="True")
 parser.add_argument("-eonv","--enable_only_normal_var", help="", type=str,  choices=["True", "true", "False", "false"], default="True")
 parser.add_argument("-eona","--enable_only_normal_arithexp", help="", type=str, choices=["True", "true", "False", "false"], default="True")
 parser.add_argument("-eond","--enable_only_normal_delta", help="", type=str, choices=["True", "true", "False", "false"], default="False")
 parser.add_argument("-cp","--checking_phase", help="", type=str,
     choices=["True", "true", "False", "false"], default="False")
 parser.add_argument("-prec","--precision", help="initial precision", type=int, default=3)
 parser.add_argument("-exp","--exponent", help="initial exponent", type=int, default=3)
 """
 parser.add_argument("-","--", help="", type=, default=)

    self.input_filename = ""
    self.error_filename = "error_solve.txt"
    self.summary_filename = "summary.txt"
    self.lift_app = "lift_stats.txt"
    self.start_time = time()
    self.iteration = 1 #iteration count
    self.abstraction = "lfp" #"lfp" for reducded precision abstraction or "real"
    self.precision = 3 #initial abstract precision when lfp
    self.max_precision = 23 #hardcoded for now for single prec
    self.refine_prec_inc = 3 #hardcoded for now
    self.exponent = 3 #initial abstract exponent when lfp
    self.max_exponent = 8 #hardcoded for now for single prec
    self.refine_exp_inc = 1 #hardcoded for now, default increase in exponent per iteration
    #for adaptive refinement
    #dictionaries with relevant data about all previous iterations
"""
 args = parser.parse_args()
 #answer = args.double * 2
 #if args.verbose == 2:
 # print("the double of {} equals {}".format(args.double, answer))
 #elif args.verbose == 1:
 # print("{}*2 == {}".format(args.double, answer))
 #else:
 # print(answer)

 #assign_to_gd(gd, args)
 write_file_for_parser(args)
 parse_sub_str='from solve_rp import *\ndict = {}\nbool={"True":True,"False":False}\nf1=open("molly.opt","r")\nfor line in f1:\n opts = line.split("|")\n dict[opts[0]] = opts[1].rstrip("\\n")\nprint dict.keys()\ngd = GlobalData()\ngd.abstraction = dict["abstraction"]\ngd.cfg_filename = dict["cfg"]\ngd.enable_delta_bounds = bool[dict["enable_delta_bounds"]]\ngd.var_selection_policy = int(dict["var_selection_policy"])\ngd.generate_benchmark=bool[dict["generate_benchmark"]]\ngd.generate_benchmark_real = bool[dict["generate_benchmark_real"]]\ngd.generate_benchmark_dreal = bool[dict["generate_bechmark_dreal"]]\ngd.try_own_assignment = dict["try_own_assignment"]\ngd.non_symbolic_model_lift = dict["non_symbolic_model_lift"]\ngd.local_search_exp_factor = dict["local_search_exp_factor"]\ngd.molly_debug_file = dict["molly_debug_file"]\ngd.overall_timeout = dict["overall_timeout"]\ngd.outer_timeout = dict["outer_timeout"]\ngd.inner_timeout = dict["inner_timeout"]\ngd.tmin_lift = dict["tmin_lift"]\ngd.enable_abstract_check = bool[dict["enable_abstract_check"]]\ngd.enable_final_fp_check = bool[dict["enable_final_fp_check"]]\ngd.enable_strict_consis_check = bool[dict["enable_strict_consis_check"]]\ngd.enable_only_normal = bool[dict["enable_only_normal"]]\ngd.enable_only_normal_var = bool[dict["enable_only_normal_var"]]\ngd.enable_only_normal_arithexp = bool[dict["enable_only_normal_arithexp"]]\ngd.enable_only_normal_delta = bool[dict["enable_only_normal_delta"]]\ngd.checking_phase = bool[dict["checking_phase"]]\ngd.precision = int(dict["precision"])\ngd.exponent = int(dict["exponent"])\n#print gd.abstraction\n#print str(gd.enable_delta_bounds)\nf1.close()'
 """

    self.enable_abstract_check = True# abstract value check, as well as fp value check
    self.enable_final_fp_check = True #enable fp value check
    self.enable_strict_consis_check = False
    self.enable_only_normal = True
    self.enable_only_normal_var = True
    self.enable_only_normal_arithexp = True
    self.enable_only_normal_delta = False
    self.checking_phase = False #is it the phase where an FP assignment is being checked wrt original formula
 """
 fread=open("read.py","w")
 fread.write(parse_sub_str)
 fread.close()
 #gd.input_filename = sys.argv[1]
 #initialize_summary_file(gd,sys.argv[1])
 #CR: remove the if, no demo code
 '''if (0 == run_option):
   demo_code()
 #CR:change below to remove real abstraction, retain SMT-LIB and realizer formats
 else:#run_option = 1 for regular run; 2 for run with artificial initial example
   if(3 == len (sys.argv) and (-1 != sys.argv[1].find(".smt2")) and "lfp"== sys.argv[2]):
     #of the form "python solve-rp.py examples/assoc4.smt2 lfp"
     gd.abstraction = "lfp"
   elif(4 == len(sys.argv)):
     #of the form "python solve-rp.py examples/fml/assoc4.fml examples/single-prec-modified2.cfg real"
     #of the form "python solve-rp.py examples/fml/assoc4.fml examples/single-prec-modified2.cfg lfp"
     gd.abstraction = sys.argv[3]
   elif (4 != len(sys.argv) or "real" != sys.argv[3]):
     myprint("Usage: python2.7 solve.py <constraint_file.smt2> lfp or python2.7 solve.py <formula_file.fml> <cfg_file.cfg> real")
     fstat.close()
     exit(1)
   #gd.abstraction = "lfp"
   '''
 #fstat.write("\n"+sys.argv[1])
 #fstat.flush()
 #os.fsync(fstat)
 print sys.argv[1:]
 globals()['gd'] = gd
 print globals()
 main(vars(args),gd)
 #main(sys.argv[1:],gd)
 fstat.close()
 frank.close()
#Notes:
#- Should n't sem_to_decimal get an exact Real (Fraction) value for all vars - can be brought down to appropriate reduced precision or full FP prec later?
# - fix: epsilon increment is to be divided by 2 for Downward Support at positive
#   power-of-two boundaries as also for Upward support at negative power-of-two boundaries

