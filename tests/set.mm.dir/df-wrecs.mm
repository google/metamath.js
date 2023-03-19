
axiom df-wrecs
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let cF: class F
  assert |- wrecs ( R , A , F ) = U. { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( F ` ( f |` Pred ( R , A , y ) ) ) ) }
end
