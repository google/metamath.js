
axiom df-cyg
  let vx: setvar x
  let vg: setvar g
  let vn: setvar n
  assert |- CycGrp = { g e. Grp | E. x e. ( Base ` g ) ran ( n e. ZZ |-> ( n ( .g ` g ) x ) ) = ( Base ` g ) }
end
