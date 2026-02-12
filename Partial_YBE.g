## A partial YB map table is a matrix T whose entries can be 
## either pairs [i->j, i<-j] or empty lists [] (if undefined).

PartialDomain := function(T)
## yields the domain (as a set, i.e. SSortedList) on which T is defined
local res, i,j;
res:= [];
for i in [1..Size(T)] do
for j in [1..Size(T)] do
if T[i][j] <> [] then Add(res, [i,j]); fi; 
od; od;
return AsSSortedList(SSortedList(res));
end;

PartialCodomain := function(T)
## yields the codomain of T as a set (SSortedList)
local res, D, d;
res:= [];
D:= PartialDomain(T);
for d in D do
Add(res, T[d[1]][d[2]]);
od;
return AsSSortedList(SSortedList(res));
end;	

