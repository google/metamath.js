include "wcel.mm"
include "csuc.mm"
include "wceq.mm"
include "wo.mm"
include "eqid.mm"
include "olci.mm"
include "elsucg.mm"
include "mpbiri.mm"

theorem sucidg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> A e. suc A )

  proof
    cA
    cV
    wcel
    cA
    cA
    csuc
    wcel
    cA
    cA
    wcel
    #
    cA
    cA
    wceq
    #
    wo
    @1
    @0
    cA
    eqid
    olci
    cA
    cA
    cV
    elsucg
    mpbiri
end
