
axiom df-siga
  let vx: setvar x
  let vo: setvar o
  let vs: setvar s
  assert |- sigAlgebra = ( o e. _V |-> { s | ( s C_ ~P o /\ ( o e. s /\ A. x e. s ( o \ x ) e. s /\ A. x e. ~P s ( x ~<_ _om -> U. x e. s ) ) ) } )
end
