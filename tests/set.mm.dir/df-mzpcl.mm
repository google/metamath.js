
axiom df-mzpcl
  let vx: setvar x
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vp: setvar p
  assert |- mzPolyCld = ( v e. _V |-> { p e. ~P ( ZZ ^m ( ZZ ^m v ) ) | ( ( A. i e. ZZ ( ( ZZ ^m v ) X. { i } ) e. p /\ A. j e. v ( x e. ( ZZ ^m v ) |-> ( x ` j ) ) e. p ) /\ A. f e. p A. g e. p ( ( f oF + g ) e. p /\ ( f oF x. g ) e. p ) ) } )
end
