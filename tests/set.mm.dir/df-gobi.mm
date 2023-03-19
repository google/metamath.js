
axiom df-gobi
  let vv: setvar v
  let vu: setvar u
  assert |- <->g = ( u e. _V , v e. _V |-> ( ( u ->g v ) /\g ( v ->g u ) ) )
end
