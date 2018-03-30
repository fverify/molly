g!/Running on \|^unsat\|^sat\|Time taken\|timed out/d
%s/.*\(\<timed out\>\).*/\1/
%s/\ntimed out/ TO TO/
%s/\nsat/ sat/
%s/\nunsat/ unsat/
%s/\nTime taken://
%s/Running on //
%s/.smt2//
