include "ax-mulcl.mm"

theorem mulcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A x. B ) e. CC )

  proof
    cA
    cB
    ax-mulcl
end
