include "ccnv.mm"
include "ccom.mm"
include "cvv.mm"
include "cres.mm"
include "cnvcnv2.mm"
include "coeq1i.mm"
include "crn.mm"
include "wss.mm"
include "wceq.mm"
include "ssv.mm"
include "cores.mm"
include "ax-mp.mm"
include "eqtri.mm"

theorem cocnvcnv1
  let cA: class A
  let cB: class B


  assert |- ( `' `' A o. B ) = ( A o. B )

  proof
    cA
    ccnv
    ccnv
    #
    cB
    ccom
    cA
    cvv
    cres
    #
    cB
    ccom
    #
    cA
    cB
    ccom
    #
    @0
    @1
    cB
    cA
    cnvcnv2
    coeq1i
    cB
    crn
    #
    cvv
    wss
    @2
    @3
    wceq
    @4
    ssv
    cA
    cB
    cvv
    cores
    ax-mp
    eqtri
end
