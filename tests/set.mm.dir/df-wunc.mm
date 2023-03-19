
axiom df-wunc
  let vx: setvar x
  let vu: setvar u
  assert |- wUniCl = ( x e. _V |-> |^| { u e. WUni | x C_ u } )
end
