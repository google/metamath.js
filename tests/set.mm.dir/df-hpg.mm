
axiom df-hpg
  let vt: setvar t
  let vg: setvar g
  let vi: setvar i
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assert |- hpG = ( g e. _V |-> ( d e. ran ( LineG ` g ) |-> { <. a , b >. | [. ( Base ` g ) / p ]. [. ( Itv ` g ) / i ]. E. c e. p ( ( ( a e. ( p \ d ) /\ c e. ( p \ d ) ) /\ E. t e. d t e. ( a i c ) ) /\ ( ( b e. ( p \ d ) /\ c e. ( p \ d ) ) /\ E. t e. d t e. ( b i c ) ) ) } ) )
end
