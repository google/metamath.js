
axiom df-s5
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assert |- <" A B C D E "> = ( <" A B C D "> ++ <" E "> )
end
