
axiom df-tsms
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vf: setvar f
  let vs: setvar s
  assert |- tsums = ( w e. _V , f e. _V |-> [_ ( ~P dom f i^i Fin ) / s ]_ ( ( ( TopOpen ` w ) fLimf ( s filGen ran ( z e. s |-> { y e. s | z C_ y } ) ) ) ` ( y e. s |-> ( w gsum ( f |` y ) ) ) ) )
end
