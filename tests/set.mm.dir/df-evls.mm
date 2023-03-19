
axiom df-evls
  let vx: setvar x
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vs: setvar s
  let vr: setvar r
  let vb: setvar b
  assert |- evalSub = ( i e. _V , s e. CRing |-> [_ ( Base ` s ) / b ]_ ( r e. ( SubRing ` s ) |-> [_ ( i mPoly ( s |`s r ) ) / w ]_ ( iota_ f e. ( w RingHom ( s ^s ( b ^m i ) ) ) ( ( f o. ( algSc ` w ) ) = ( x e. r |-> ( ( b ^m i ) X. { x } ) ) /\ ( f o. ( i mVar ( s |`s r ) ) ) = ( x e. i |-> ( g e. ( b ^m i ) |-> ( g ` x ) ) ) ) ) ) )
end
