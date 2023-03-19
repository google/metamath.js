include "cc.mm"
include "chil.mm"
include "csp.mm"
include "ax-hfi.mm"
include "fovcl.mm"

theorem hicl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A .ih B ) e. CC )

  proof
    cA
    cB
    cc
    chil
    chil
    csp
    ax-hfi
    fovcl
end
