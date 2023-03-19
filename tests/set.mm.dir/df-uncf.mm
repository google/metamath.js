
axiom df-uncf
  let vf: setvar f
  let vc: setvar c
  assert |- uncurryF = ( c e. _V , f e. _V |-> ( ( ( c ` 1 ) evalF ( c ` 2 ) ) o.func ( ( f o.func ( ( c ` 0 ) 1stF ( c ` 1 ) ) ) pairF ( ( c ` 0 ) 2ndF ( c ` 1 ) ) ) ) )
end
