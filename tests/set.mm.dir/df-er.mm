
axiom df-er
  let cA: class A
  let cR: class R
  assert |- ( R Er A <-> ( Rel R /\ dom R = A /\ ( `' R u. ( R o. R ) ) C_ R ) )
end
