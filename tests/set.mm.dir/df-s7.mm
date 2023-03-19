
axiom df-s7
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  assert |- <" A B C D E F G "> = ( <" A B C D E F "> ++ <" G "> )
end
