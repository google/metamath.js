
axiom df-cplmet
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assert |- cplMetSp = ( w e. _V |-> [_ ( ( w ^s NN ) |`s ( Cau ` ( dist ` w ) ) ) / r ]_ [_ ( Base ` r ) / v ]_ [_ { <. f , g >. | ( { f , g } C_ v /\ A. x e. RR+ E. j e. ZZ ( f |` ( ZZ>= ` j ) ) : ( ZZ>= ` j ) --> ( ( g ` j ) ( ball ` ( dist ` w ) ) x ) ) } / e ]_ ( ( r /s e ) sSet { <. ( dist ` ndx ) , { <. <. x , y >. , z >. | E. p e. v E. q e. v ( ( x = [ p ] e /\ y = [ q ] e ) /\ ( p oF ( dist ` r ) q ) ~~> z ) } >. } ) )
end
