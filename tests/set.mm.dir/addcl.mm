include "ax-addcl.mm"

theorem addcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A + B ) e. CC )

  proof
    cA
    cB
    ax-addcl
end
