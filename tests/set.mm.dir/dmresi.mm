include "cid.mm"
include "cdm.mm"
include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "cvv.mm"
include "ssv.mm"
include "dmi.mm"
include "sseqtr4i.mm"
include "ssdmres.mm"
include "mpbi.mm"

theorem dmresi
  let cA: class A


  assert |- dom ( _I |` A ) = A

  proof
    cA
    cid
    cdm
    #
    wss
    cid
    cA
    cres
    cdm
    cA
    wceq
    cA
    cvv
    @0
    cA
    ssv
    dmi
    sseqtr4i
    cA
    cid
    ssdmres
    mpbi
end
