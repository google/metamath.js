include "ax-addcl.mm"

theorem addcl
  param cA: class A
  param cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A + B ) e. CC )

  proof
    cA
    cB
    ax-addcl
end
