
axiom df-s8
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  assert |- <" A B C D E F G H "> = ( <" A B C D E F G "> ++ <" H "> )
end
