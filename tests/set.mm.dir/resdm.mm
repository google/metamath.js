include "wrel.mm"
include "cdm.mm"
include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "ssid.mm"
include "relssres.mm"
include "mpan2.mm"

theorem resdm
  let cA: class A


  assert |- ( Rel A -> ( A |` dom A ) = A )

  proof
    cA
    wrel
    cA
    cdm
    #
    @0
    wss
    cA
    @0
    cres
    cA
    wceq
    @0
    ssid
    cA
    @0
    relssres
    mpan2
end
