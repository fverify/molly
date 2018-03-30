import sys,re
from collections import OrderedDict
#import solve
 
class GlobalData:
  def __init__(self):
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
    self.ordered=OrderedDict()
    self.initialization =  ""
  
  def increment_index(self):
    self.new_index+=1

def PRINT_DEBUG(gd,x):
  #print (x)
  gd.initialization+=x+"\n"

#gd = GlobalData()
def rename(original):
  return "lit_"+original.lstrip(".")

def rename_new(original,gd):
  return original+"_new"+str(gd.new_index)

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
            PRINT_DEBUG(gd,lhs+"=PropExp("+rename(opnd)+",'not',None)") 
        else: 
            opnd2=toks[6].rstrip("\n").rstrip(")")
            PRINT_DEBUG(gd,lhs+"=PropExp("+rename(toks[5])+",'"+operator+"',"+rename(opnd2)+")")
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


def main(argv,gd):
  #gd = GlobalData()
  f1 = open(argv[0],"r") 
  for line in f1:
    #PRINT_DEBUG(gd,line.rstrip("\n"))
    parse(line,gd)
  f1.close()
  #print_tokens(gd)
  #PRINT_DEBUG(gd,"#Vars:")
  #for var in gd.avars.keys():
  #  PRINT_DEBUG(gd,var)
  #PRINT_DEBUG(gd,"#Consts:")
  #for var in gd.consts.keys():
  #  PRINT_DEBUG(gd,var)

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
  
if __name__ == "__main__":
  gd= GlobalData()
  if(2 != len(sys.argv)):
    PRINT_DEBUG(gd,"Usage: python2.7 parser.py <griggio-benchmark.smt2>")
    sys.exit(1)
  else:
    PRINT_DEBUG(gd,"import gmpy2")
    PRINT_DEBUG(gd,"from solve import *")
    #adding dummy variables if necessary
    extra_str="const_1 = Const(mpfr(Fraction('1')),Fraction('1'))\nconst_2 = Const(mpfr(Fraction('2')),Fraction('2'))\nrelexp_1 = RelExp(const_1,'<',const_2)\nprop_1 = Prop('prop_1',relexp_1)\n#propexp = PropExp(propexp,'and',prop_1)\n"
    main(sys.argv[1:],gd)
    #exit(1)
    top_level_objects = gd.asserts.keys()+gd.new_asserts.keys()
    if(1==len(top_level_objects)):
      gd.consts['const_1']='const_1'
      gd.ordered['const_1']='const_1'
      gd.consts['const_2']='const_2'
      gd.ordered['const_2']='const_2'
      gd.relexps['relexp_1']='relexp_1'
      gd.ordered['relexp_1']='relexp_1'
      gd.props['prop_1']='prop_1'
      gd.ordered['prop_1']='prop_1'
      PRINT_DEBUG(gd,extra_str)
      final_str="PropExp("+str(top_level_objects[0])+",'and',prop_1)"
    else:
      final_str = generate_constraint(top_level_objects,"","",len(top_level_objects)) 
    gd.propexps['propexp']='propexp'
    gd.ordered['propexp']='propexp'
    PRINT_DEBUG(gd,"propexp="+final_str+"\nprint propexp.preorder()\n")

  print gd.initialization


  #generate_smtlib(gd)   
    #for var in gd.asserts.keys()+gd.new_asserts.keys():
    #  PRINT_DEBUG(gd,"print "+var+".preorder()")
# TODO:
# stack depth issue in python, (change MAXSTACK in Parser.h AND recompile python) OR (flatten out the final PropExp calls and change generate_constraint to a non-recursive def)
# - Checking for/reporting double type (11 53)
# - Checking for/reporting cast
# - Cross-check : Can a prop or propexp use '='?
