
axiom df-nmop
  let vx: setvar x
  let vz: setvar z
  let vt: setvar t
  assert |- normop = ( t e. ( ~H ^m ~H ) |-> sup ( { x | E. z e. ~H ( ( normh ` z ) <_ 1 /\ x = ( normh ` ( t ` z ) ) ) } , RR* , < ) )
end
