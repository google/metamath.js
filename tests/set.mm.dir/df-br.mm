

axiom df-br
  param cA: class A
  param cB: class B
  param cR: class R
  assert |- ( A R B <-> <. A , B >. e. R )
end
