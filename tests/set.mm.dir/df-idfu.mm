
axiom df-idfu
  let vz: setvar z
  let vt: setvar t
  let vb: setvar b
  assert |- idFunc = ( t e. Cat |-> [_ ( Base ` t ) / b ]_ <. ( _I |` b ) , ( z e. ( b X. b ) |-> ( _I |` ( ( Hom ` t ) ` z ) ) ) >. )
end
