
axiom df-pj
  let vx: setvar x
  let vh: setvar h
  assert |- proj = ( h e. _V |-> ( ( x e. ( LSubSp ` h ) |-> ( x ( proj1 ` h ) ( ( ocv ` h ) ` x ) ) ) i^i ( _V X. ( ( Base ` h ) ^m ( Base ` h ) ) ) ) )
end
