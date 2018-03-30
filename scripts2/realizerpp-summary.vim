#:%s/\/home\/jaideep\/repositories\/fpa-heterogeneous\/decision-procedure\/abstraction\/code\/misc\/benchmarks\/griggio\///g
:%s/\/home\/jaideep\/repositories\/fpa-heterogeneous\/decision-procedure\/abstraction\/code\/examples\/polynomials\/fml\///g
:%s/\nsat/ sat/g
:%s/\nunsat/ unsat/g
:%s/\ntime://g
:%s/\niteration: / /g
::%g!/sat\|unsat/d
:%s/ lift//g
:%s/#####//g
:%s/\\.fml//g
:%s/\\.smt2//g

