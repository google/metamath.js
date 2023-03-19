
axiom df-wlim
  let vx: setvar x
  let cA: class A
  let cR: class R
  assert |- WLim ( R , A ) = { x e. A | ( x =/= inf ( A , A , R ) /\ x = sup ( Pred ( R , A , x ) , A , R ) ) }
end
