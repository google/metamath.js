
axiom df-altop
  let cA: class A
  let cB: class B
  assert |- << A , B >> = { { A } , { A , { B } } }
end
