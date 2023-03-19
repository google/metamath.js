
axiom df-lmod
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vt: setvar t
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  assert |- LMod = { g e. Grp | [. ( Base ` g ) / v ]. [. ( +g ` g ) / a ]. [. ( Scalar ` g ) / f ]. [. ( .s ` g ) / s ]. [. ( Base ` f ) / k ]. [. ( +g ` f ) / p ]. [. ( .r ` f ) / t ]. ( f e. Ring /\ A. q e. k A. r e. k A. x e. v A. w e. v ( ( ( r s w ) e. v /\ ( r s ( w a x ) ) = ( ( r s w ) a ( r s x ) ) /\ ( ( q p r ) s w ) = ( ( q s w ) a ( r s w ) ) ) /\ ( ( ( q t r ) s w ) = ( q s ( r s w ) ) /\ ( ( 1r ` f ) s w ) = w ) ) ) }
end
