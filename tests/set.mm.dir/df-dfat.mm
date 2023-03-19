
axiom df-dfat
  let cA: class A
  let cF: class F
  assert |- ( F defAt A <-> ( A e. dom F /\ Fun ( F |` { A } ) ) )
end
