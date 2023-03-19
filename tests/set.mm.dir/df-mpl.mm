
axiom df-mpl
  let vw: setvar w
  let vf: setvar f
  let vi: setvar i
  let vr: setvar r
  assert |- mPoly = ( i e. _V , r e. _V |-> [_ ( i mPwSer r ) / w ]_ ( w |`s { f e. ( Base ` w ) | f finSupp ( 0g ` r ) } ) )
end
