from gmpy2 import *
ctx=get_context()
#print ctx
ctx.precision=4
ctx.emax=3
ctx.emin=-3
print ctx
a1=mpfr('0.34375')
a2=mpfr('0.375')
a3=mpfr('0.15625')
aexp2=a1+a2
aexp=aexp2+a3

aexp3=a2+a3
aexp1=a1+aexp3

res = (aexp > aexp1)
print "(a1+a2)+a3 > a1+(a2+a3): "+str(res)

print "a1:         {0:.8Df}".format(a1)
print "a2:         {0:.8Df}".format(a2)
print "a3:         {0:.8Df}".format(a3)
print "a1+a2:      {0:.8Df}".format(aexp2)
print "(a1+a2)+a3: {0:.8Df}".format(aexp)
print "a2+a3:      {0:.8Df}".format(aexp3)
print "a1+(a2+a3): {0:.8Df}".format(aexp1)


#print "{0:.65Df}".format(c)
#arithexp2 = ArithExp(a1,'+',a2)
#arithexp = ArithExp(arithexp2,'+',a3)
#arithexp3 = ArithExp(a2,'+',a3)
#arithexp1 = ArithExp(a1,'+',arithexp3)
#relexp = RelExp(arithexp,'>',arithexp1)
#prop = Prop('prop',relexp)
#const0 = Const(mpfr('1'),Fraction(str(mpfr('1'))))
#const1 = Const(mpfr('2'),Fraction(str(mpfr('2'))))
#relexp1 = RelExp(const0,'<',const1)
#prop1 = Prop('prop1',relexp1)
#propexp = PropExp(prop,'and',prop1)
