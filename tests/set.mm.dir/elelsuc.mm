include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "wo.mm"
include "orc.mm"
include "elsucg.mm"
include "mpbird.mm"

theorem elelsuc
  let cA: class A
  let cB: class B


  assert |- ( A e. B -> A e. suc B )

  proof
    cA
    cB
    wcel
    #
    cA
    cB
    csuc
    wcel
    @0
    cA
    cB
    wceq
    #
    wo
    @0
    @1
    orc
    cA
    cB
    cB
    elsucg
    mpbird
end
