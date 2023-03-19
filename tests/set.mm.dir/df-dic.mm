
axiom df-dic
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  assert |- DIsoC = ( k e. _V |-> ( w e. ( LHyp ` k ) |-> ( q e. { r e. ( Atoms ` k ) | -. r ( le ` k ) w } |-> { <. f , s >. | ( f = ( s ` ( iota_ g e. ( ( LTrn ` k ) ` w ) ( g ` ( ( oc ` k ) ` w ) ) = q ) ) /\ s e. ( ( TEndo ` k ) ` w ) ) } ) ) )
end
