
axiom df-nmfn
  let vx: setvar x
  let vz: setvar z
  let vt: setvar t
  assert |- normfn = ( t e. ( CC ^m ~H ) |-> sup ( { x | E. z e. ~H ( ( normh ` z ) <_ 1 /\ x = ( abs ` ( t ` z ) ) ) } , RR* , < ) )
end
