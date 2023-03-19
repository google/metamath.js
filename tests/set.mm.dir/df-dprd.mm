
axiom df-dprd
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  assert |- DProd = ( g e. Grp , s e. { h | ( h : dom h --> ( SubGrp ` g ) /\ A. x e. dom h ( A. y e. ( dom h \ { x } ) ( h ` x ) C_ ( ( Cntz ` g ) ` ( h ` y ) ) /\ ( ( h ` x ) i^i ( ( mrCls ` ( SubGrp ` g ) ) ` U. ( h " ( dom h \ { x } ) ) ) ) = { ( 0g ` g ) } ) ) } |-> ran ( f e. { h e. X_ x e. dom s ( s ` x ) | h finSupp ( 0g ` g ) } |-> ( g gsum f ) ) )
end
