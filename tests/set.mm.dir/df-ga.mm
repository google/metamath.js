
axiom df-ga
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vg: setvar g
  let vm: setvar m
  let vs: setvar s
  let vb: setvar b
  assert |- GrpAct = ( g e. Grp , s e. _V |-> [_ ( Base ` g ) / b ]_ { m e. ( s ^m ( b X. s ) ) | A. x e. s ( ( ( 0g ` g ) m x ) = x /\ A. y e. b A. z e. b ( ( y ( +g ` g ) z ) m x ) = ( y m ( z m x ) ) ) } )
end
