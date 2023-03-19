
axiom ax-pre-ltadd
  let cA: class A
  let cB: class B
  let cC: class C
  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A <RR B -> ( C + A ) <RR ( C + B ) ) )
end
