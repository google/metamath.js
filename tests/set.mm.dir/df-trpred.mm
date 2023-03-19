
axiom df-trpred
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cX: class X
  let va: setvar a
  assert |- TrPred ( R , A , X ) = U. ran ( rec ( ( a e. _V |-> U_ y e. a Pred ( R , A , y ) ) , Pred ( R , A , X ) ) |` _om )
end
