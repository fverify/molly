g!/Running on \|Iteration count:\|^unsat\|^sat\|Time taken\|timed out/d
%s/.*\(\<timed out\>\).*/\1/
%s/\nIteration count://
%s/\nTime taken://
%s/\nsat/ sat/
%s/\nunsat/ unsat/
:%s/\ntimed out/ X TO TO/
%s/Running on //
