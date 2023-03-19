
axiom ax-pre-lttrn
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A <RR B /\ B <RR C ) -> A <RR C ) )
end
