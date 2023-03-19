include "wrel.mm"
include "ccnv.mm"
include "wss.mm"
include "wa.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "dfrel2.mm"
include "eqss.mm"
include "bitri.mm"
include "cnvcnvss.mm"
include "biantrur.mm"
include "ssdif0.mm"
include "3bitr2i.mm"

theorem relnonrel
  let cA: class A


  assert |- ( Rel A <-> ( A \ `' `' A ) = (/) )

  proof
    cA
    wrel
    #
    cA
    ccnv
    ccnv
    #
    cA
    wss
    #
    cA
    @1
    wss
    #
    wa
    #
    @3
    cA
    @1
    cdif
    c0
    wceq
    @0
    @1
    cA
    wceq
    @4
    cA
    dfrel2
    @1
    cA
    eqss
    bitri
    @2
    @3
    cA
    cnvcnvss
    biantrur
    cA
    @1
    ssdif0
    3bitr2i
end
