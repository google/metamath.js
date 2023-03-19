
axiom ax-pre-lttri
  let cA: class A
  let cB: class B
  assert |- ( ( A e. RR /\ B e. RR ) -> ( A <RR B <-> -. ( A = B \/ B <RR A ) ) )
end
