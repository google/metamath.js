
axiom df-afv
  let vx: setvar x
  let cA: class A
  let cF: class F
  assert |- ( F ''' A ) = if ( F defAt A , ( iota x A F x ) , _V )
end
