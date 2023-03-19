
axiom df-polarityN
  let vm: setvar m
  let vp: setvar p
  let vl: setvar l
  assert |- _|_P = ( l e. _V |-> ( m e. ~P ( Atoms ` l ) |-> ( ( Atoms ` l ) i^i |^|_ p e. m ( ( pmap ` l ) ` ( ( oc ` l ) ` p ) ) ) ) )
end
