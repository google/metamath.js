
axiom df-resv
  let vx: setvar x
  let vw: setvar w
  assert |- |`v = ( w e. _V , x e. _V |-> if ( ( Base ` ( Scalar ` w ) ) C_ x , w , ( w sSet <. ( Scalar ` ndx ) , ( ( Scalar ` w ) |`s x ) >. ) ) )
end
