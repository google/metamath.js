include "wceq.mm"
include "csuc.mm"
include "sucid.mm"
include "suceq.mm"
include "syl5eleq.mm"

theorem eqelsuc
  let cA: class A
  let cB: class B
  assume eqelsuc.1: |- A e. _V


  assert |- ( A = B -> A e. suc B )

  proof
    cA
    cB
    wceq
    cA
    cA
    csuc
    cB
    csuc
    cA
    eqelsuc.1
    sucid
    cA
    cB
    suceq
    syl5eleq
end
