
axiom df-wsuc
  let cA: class A
  let cR: class R
  let cX: class X
  assert |- wsuc ( R , A , X ) = inf ( Pred ( `' R , A , X ) , A , R )
end
