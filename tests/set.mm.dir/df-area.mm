
axiom df-area
  let vx: setvar x
  let vt: setvar t
  let vs: setvar s
  assert |- area = ( s e. { t e. ~P ( RR X. RR ) | ( A. x e. RR ( t " { x } ) e. ( `' vol " RR ) /\ ( x e. RR |-> ( vol ` ( t " { x } ) ) ) e. L^1 ) } |-> S. RR ( vol ` ( s " { x } ) ) _d x )
end
