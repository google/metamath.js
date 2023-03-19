
axiom df-orng
  let vz: setvar z
  let vv: setvar v
  let vt: setvar t
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vl: setvar l
  assert |- oRing = { r e. ( Ring i^i oGrp ) | [. ( Base ` r ) / v ]. [. ( 0g ` r ) / z ]. [. ( .r ` r ) / t ]. [. ( le ` r ) / l ]. A. a e. v A. b e. v ( ( z l a /\ z l b ) -> z l ( a t b ) ) }
end
