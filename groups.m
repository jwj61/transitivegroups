// Input to functions are either n,t or a group g

function tg(n,t)
  return TransitiveGroup(n,t);
end function;

function bool2int(b)
  if b eq true then return 1; end if;
  return 0;
end function;

function basicdata(g)
  dat := <IsCyclic(g), IsSolvable(g), Order(g), IsEven(g), IsAbelian(g)>;
  return <bool2int(b) : b in dat>;
end function;

function autorder(g,n)
  return Order(Centralizer(SymmetricGroup(n), g));
end function;

