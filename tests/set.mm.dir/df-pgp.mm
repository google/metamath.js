
axiom df-pgp
  let vx: setvar x
  let vg: setvar g
  let vn: setvar n
  let vp: setvar p
  assert |- pGrp = { <. p , g >. | ( ( p e. Prime /\ g e. Grp ) /\ A. x e. ( Base ` g ) E. n e. NN0 ( ( od ` g ) ` x ) = ( p ^ n ) ) }
end
