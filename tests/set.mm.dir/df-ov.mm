

axiom df-ov
  param cA: class A
  param cB: class B
  param cF: class F
  assert |- ( A F B ) = ( F ` <. A , B >. )
end
