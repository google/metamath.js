
axiom df-gcdOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  assert |- gcdOLD ( A , B ) = sup ( { x e. NN | ( ( A / x ) e. NN /\ ( B / x ) e. NN ) } , NN , < )
end
