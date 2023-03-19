include "wrel.mm"
include "cdm.mm"
include "cvv.mm"
include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "ssv.mm"
include "relssres.mm"
include "mpan2.mm"

theorem residOLD
  let cA: class A


  assert |- ( Rel A -> ( A |` _V ) = A )

  proof
    cA
    wrel
    cA
    cdm
    #
    cvv
    wss
    cA
    cvv
    cres
    cA
    wceq
    @0
    ssv
    cA
    cvv
    relssres
    mpan2
end
