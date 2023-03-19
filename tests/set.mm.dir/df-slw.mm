
axiom df-slw
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vp: setvar p
  assert |- pSyl = ( p e. Prime , g e. Grp |-> { h e. ( SubGrp ` g ) | A. k e. ( SubGrp ` g ) ( ( h C_ k /\ p pGrp ( g |`s k ) ) <-> h = k ) } )
end
