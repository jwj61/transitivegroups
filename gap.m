// Compute gap ids of groups

function gapid(g)
  try
    gid := IdentifyGroup(g);
    return gid[2];
  catch e
    return 0;
  end try;
end function;

l:=[[ gapid(TransitiveGroup(n,t)) :  t in [1..NumberOfTransitiveGroups(n)]] : n in [1..23]];
