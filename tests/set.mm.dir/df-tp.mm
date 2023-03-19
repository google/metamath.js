
axiom df-tp
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- { A , B , C } = ( { A , B } u. { C } )
end
