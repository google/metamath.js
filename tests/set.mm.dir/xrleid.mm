include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "eqid.mm"
include "olci.mm"
include "xrleloe.mm"
include "mpbiri.mm"
include "anidms.mm"

theorem xrleid
  let cA: class A


  assert |- ( A e. RR* -> A <_ A )

  proof
    cA
    cxr
    wcel
    #
    cA
    cA
    cle
    wbr
    #
    @0
    @0
    wa
    @1
    cA
    cA
    clt
    wbr
    #
    cA
    cA
    wceq
    #
    wo
    @3
    @2
    cA
    eqid
    olci
    cA
    cA
    xrleloe
    mpbiri
    anidms
end
