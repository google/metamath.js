
axiom df-qtop
  let vf: setvar f
  let vj: setvar j
  let vs: setvar s
  assert |- qTop = ( j e. _V , f e. _V |-> { s e. ~P ( f " U. j ) | ( ( `' f " s ) i^i U. j ) e. j } )
end
