
axiom df-s6
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assert |- <" A B C D E F "> = ( <" A B C D E "> ++ <" F "> )
end
