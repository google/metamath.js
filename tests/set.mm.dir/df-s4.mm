
axiom df-s4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assert |- <" A B C D "> = ( <" A B C "> ++ <" D "> )
end
