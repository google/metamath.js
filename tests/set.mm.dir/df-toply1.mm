
axiom df-toply1
  let vf: setvar f
  let vn: setvar n
  assert |- toPoly1 = ( f e. _V |-> ( n e. ( NN0 ^m 1o ) |-> ( f ` ( n ` (/) ) ) ) )
end
