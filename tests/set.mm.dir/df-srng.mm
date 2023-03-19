
axiom df-srng
  let vf: setvar f
  let vi: setvar i
  assert |- *Ring = { f | [. ( *rf ` f ) / i ]. ( i e. ( f RingHom ( oppR ` f ) ) /\ i = `' i ) }
end
