
axiom df-nacs
  let vx: setvar x
  let vg: setvar g
  let vs: setvar s
  let vc: setvar c
  assert |- NoeACS = ( x e. _V |-> { c e. ( ACS ` x ) | A. s e. c E. g e. ( ~P x i^i Fin ) s = ( ( mrCls ` c ) ` g ) } )
end
