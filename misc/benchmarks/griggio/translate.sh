#!/bin/sh

for i in *.smt2; do sed -i -e 's/Float/FP/' $i; done
for i in *.smt2; do sed -i -e 's/fp_round_nearest_even/roundNearestTiesToEven/' $i; done
for i in *.smt2; do sed -i -e 's/fp_round_nearest_away/roundNearestTiesToAway/' $i; done
for i in *.smt2; do sed -i -e 's/fpadd/+/' $i; done
for i in *.smt2; do sed -i -e 's/fple/<=/' $i; done
for i in *.smt2; do sed -i -e 's/fplt/</' $i; done
for i in *.smt2; do sed -i -e 's/fpneg/-/' $i; done
for i in *.smt2; do sed -i -e 's/\+inf/plusInfinity/' $i; done
for i in *.smt2; do sed -i -e 's/-inf/minusInfinity/' $i; done
for i in *.smt2; do sed -i -e 's/fpcast/asFloat/' $i; done
for i in *.smt2; do sed -i -e 's/fpnum/fromIEEEInt/' $i; done


for i in *.smt2; do sed -i -e 's/(_ plusInfinity 11 52)/(as plusInfinity (_ FP 11 53))/' $i; done
for i in *.smt2; do sed -i -e 's/(_ minusInfinity 11 52)/(as minusInfinity (_ FP 11 53))/' $i; done

for i in *.smt2; do sed -i -e 's/8 23/8 24/' $i; done
for i in *.smt2; do sed -i -e 's/11 52/11 53/' $i; done
