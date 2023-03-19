
axiom df-intop
  let vm: setvar m
  let vn: setvar n
  assert |- intOp = ( m e. _V , n e. _V |-> ( n ^m ( m X. m ) ) )
end
