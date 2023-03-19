
axiom df-topsep
  let vx: setvar x
  let vj: setvar j
  assert |- TopSep = { j e. Top | E. x e. ~P U. j ( x ~<_ _om /\ ( ( cls ` j ) ` x ) = U. j ) }
end
