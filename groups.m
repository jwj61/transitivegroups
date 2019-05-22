// Input to functions are either n,t or a group g

mycut := 47; // Not used
SetColumns(0);

ccomp := function(u,v)
  if u[1] eq v[1] then
    if u[2][1] eq v[2][1] then
      return(u[2][2] - v[2][2]);
    else
      return(u[2][1] - v[2][1]);
    end if;
  else
    return(u[1]-v[1]);
  end if;
end function;

ccomp2 := function(u,v)
  if u[1][1] eq v[1][1] then
    return(u[1][2]-v[1][2]);
  end if;
  return(u[1][1] - v[1][1]);
end function;

function fixstring(inst)
  return "\"" cat inst cat "\"";
end function;

function tg(n,t)
  return TransitiveGroup(n,t);
end function;

function bool2int(b)
  if b eq true then return 1; end if;
  return 0;
end function;

function basicdata(g)
  return <bool2int(IsCyclic(g)), bool2int(IsSolvable(g)), Order(g), bool2int(IsEven(g)), bool2int(IsAbelian(g))>;
end function;

function autorder(g,n)
  return Order(Centralizer(SymmetricGroup(n), g));
end function;

sibl := function(g,s)
  printf "sibling, ";
  s1:=Stabilizer(g,1);
  good := [z : z in s | Order(Core(g,z)) eq 1];
  good := [z : z in good | not IsConjugate(g,s1,z)];
  ans:=AssociativeArray();
  printf "loop %o, ", #good;
  // if #good gt 20000 then
  //   return [[[-1,0], [#good,0]]];
  // end if;
  for j in good do 
    tt,nn :=TransitiveGroupIdentification(CosetImage(g, j));
    old, howmany := IsDefined(ans,[nn,tt]);
    if old then
      ans[[nn,tt]] := ans[[nn,tt]] + 1;
    else
      ans[[nn,tt]] := 1;
    end if;
  end for;
  sibs:=[];
  for ky in Keys(ans) do
    if sibs eq [] then
      sibs := [[ky, [ans[ky],0]]];
    else
      Append(~sibs, [ky,[ans[ky],0]]); 
    end if;
  end for;
  return Sort(sibs);
end function;

// Find resolvents by low index subgroups, not by normal subs
res2 := function(g,s)
  printf "resolvents, ";
  s1:=Stabilizer(g,1);
  hcore := [[z, Core(g,z)] : z in s];
  good := [z : z in hcore | Order(z[2]) gt 1];
  // if #good gt 20000 then
  //   return [<-1,[0,0], #good>];
  // end if;
  candidates:=AssociativeArray();
  sibs:=[];
  printf "loop %o, ", #good;
  for j in good do 
    tt,nn :=TransitiveGroupIdentification(CosetImage(g, j[1]));
    match,what:=IsDefined(candidates, j[2]);
    if match then
      if (nn lt what[1]) or (nn eq what[1] and tt lt what[2]) then
        candidates[j[2]] := [nn,tt];
      end if;
    else
      candidates[j[2]] := [nn,tt];
    end if;
  end for;
  res1 := [<Index(g, z), candidates[z]> : z in Keys(candidates)];
  resmu:=Multiset(res1);
  bases:=SetToSequence(Set(resmu));
  together:=[<z[1],z[2],Multiplicity(resmu, z)> : z in bases];
  Sort(~together);

  return together;
end function;

// Do cycle types match for these permutation groups?
matching := function(f, cc)
  for j in cc do
    if CycleStructure(j) ne CycleStructure(f(j)) then
          return false;
        end if;
  end for;
  return true;
end function;

twin := function(g,n,s)
  // printf "t = %o\n", t;
  s1 :=Stabilizer(g,1);
  ns1 := Order(s1);
  s:= [z : z in s | Order(z) eq ns1];
  good := [z : z in s | Order(Core(g,z)) eq 1];
  good := [z : z in good | not IsConjugate(g,s1,z)];
  if #good eq 0 then return 0; end if;
  // Now have trivial core, and not the standard sub
  cc:= [z[3] : z in Classes(g)];
  cnt:=0;
  for j in good do
    ff, g1:= CosetAction(g, j);
        if matching(ff, cc) then
      cnt := cnt+1;
        end if;
  end for;
  return cnt;
end function;

mylookup := function(g)
  high := 1;
  nn:=0;
  tt:=0;
  // printf "   lookup group of order %o\n", Order(g);
  while true do
    if high gt Order(g) then
      return <Order(g), [nn, tt]>;
    end if;
    low := high + 1;
    high := low + 20;
    s:=LowIndexSubgroups(g,<low,high>);
    Sort(~s, func<x,y | Order(y)-Order(x)>); // decreasing size
    nn:=1000000000; // Too big to ever win
    tt:=0;
    // printf "         testing list of length %o\n", #s;
    for x in s do
      if Order(Core(g,x)) eq 1 then
        n := Index(g,x);
        // printf "         testing index %o, holding %o\n", n, nn;
        if nn lt n then
          return <Order(g), [nn, tt]>;
        end if;
        if n le mycut then
          b :=CosetImage(g,x);
          t,n:=TransitiveGroupIdentification(b);
          if n lt nn then
            nn := n;
            tt := t;
          else // n == nn
            if t lt tt then
              tt := t;
            end if;
          end if;
        else
          return <Order(g), [n, -1]>;
        end if;
      end if;
    end for;
    if nn lt 1000000000 then
      return <Order(g), [nn, tt]>;
    end if;
  end while;
end function;

getreses := function(g)
  tt,nn:=TransitiveGroupIdentification(g);
  printf "Doing group %o, %o\n", nn, tt;
  ns := NormalSubgroups(g);
  ns2 := [];
  for y in ns do
    x := y`subgroup;
    if Order(x) gt 1 and Order(x) lt Order(g) then
      Append(~ns2, g/x);
    end if;
  end for;
  res1 := [mylookup(j) : j in ns2];
  Sort(~res1, ccomp2);
  return(res1);
end function;

isnewconj := function(g, li, h)
  for j in li do
    if IsConjugate(g, j, h) then 
      return(false);
    end if;
  end for;
  return(true);
end function;

subfields := function(g)
  printf "subfields\n";
  g1 := Stabilizer(g,1);
  ints := IntermediateSubgroups(g,g1);
  crlist := [];
  ans2 := AssociativeArray();
  for h in ints do
    if isnewconj(g, crlist, h) then
      tt1, nn1:=TransitiveGroupIdentification(CosetImage(g,h));
      match,what:=IsDefined(ans2, [nn1,tt1]);
      if match then
        ans2[[nn1,tt1]] +:= 1;
      else
        ans2[[nn1,tt1]] := 1;
      end if;
      Append(~crlist, h);
    end if;
  end for;
  ans3 := [<z, ans2[z]> : z in Keys(ans2)];
  Sort(~ans3);
  return(ans3);
end function;

getgens:= function(g)
  u:=SetToSequence(Generators(g));
  v:=<CycleDecomposition(uu) : uu in u>;
  vv:=<<[foo[s] : s in [1..#foo]] : foo in aa > : aa in v>;
  // Remove 1-cycles
  return <<z : z in y | #z gt 1> : y in vv>;
end function;

doall := function(n,t, thecut)
  printf "Doing group %o, %o\n", n, t;
  g := tg(n,t);
  printf "Getting low index,";
  s:=LowIndexSubgroups(g,<2,thecut>);
  thisord := Order(g);
  printf " identifying, ";
  if CanIdentifyGroup(thisord) then
    gapid:=IdentifyGroup(g)[2];
  else
    gapid:=0;
  end if;
  if n lt 20 then
    tgstring := TransitiveGroupDescription(g);
  else
    tgstring := "t" cat IntegerToString(n) cat "n" cat IntegerToString(t);
  end if;
  gens := getgens(g);
  ncc := #ConjugacyClasses(g);
  atwin := -1;
  if n ge thecut then
    atwin := twin(g,n,s);
  end if;
  return <bool2int(IsAbelian(g)), atwin,
          autorder(g,n), bool2int(IsCyclic(g)), gapid, n, thisord,
          bool2int(IsEven(g)), bool2int(IsPrimitive(g)), sibl(g,s), 
          res2(g,s), bool2int(IsSolvable(g)), subfields(g), t, tgstring,
          thecut, thecut, ncc, gens>;
end function;

// Compute siblings in higher degrees
incsib := function(n,t, low, high)
  printf "Doing group %o, %o\n", n, t;
  g := tg(n,t);
  printf "Getting low index,";
  s:=LowIndexSubgroups(g,<low,high>);
  thisord := Order(g);
  atwin := -1;
  if (n ge low) and (n le high) then
    atwin := twin(g,n,s);
  end if;
  return <n, t, atwin, sibl(g,s), high>;
end function;

// Compute resolvents in higher degrees, have to start over
incres := function(n,t, high)
  printf "Doing group %o, %o\n", n, t;
  g := tg(n,t);
  printf "Getting low index,";
  s:=LowIndexSubgroups(g,<2,high>);
  return <n, t, res2(g,s), high>;
end function;


domany := function(l,h, thecut)
  return <<doall(n,t, thecut) : t in [1..NumberOfTransitiveGroups(n)]>: n in [l..h]>;
end function;

// Only use this if we have everything below lowcut
incmany := function(deg, lowcut, highcut)
  return <incsib(deg, t, lowcut, highcut) : t in [1..NumberOfTransitiveGroups(deg)]>;
end function;
