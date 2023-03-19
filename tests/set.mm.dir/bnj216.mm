include "csuc.mm"
include "wceq.mm"
include "wcel.mm"
include "sucid.mm"
include "eleq2.mm"
include "mpbiri.mm"

theorem bnj216
  let cA: class A
  let cB: class B
  assume bnj216.1: |- B e. _V


  assert |- ( A = suc B -> B e. A )

  proof
    cA
    cB
    csuc
    #
    wceq
    cB
    cA
    wcel
    cB
    @0
    wcel
    cB
    bnj216.1
    sucid
    cA
    @0
    cB
    eleq2
    mpbiri
end
