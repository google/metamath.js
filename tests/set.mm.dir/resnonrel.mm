include "ccnv.mm"
include "cdif.mm"
include "cres.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "cvv.mm"
include "ssv.mm"
include "ssres2.mm"
include "ax-mp.mm"
include "cnvnonrel.mm"
include "cnveqi.mm"
include "cnvcnv2.mm"
include "cnv0.mm"
include "3eqtr3i.mm"
include "sseqtri.mm"
include "ss0b.mm"
include "mpbi.mm"

theorem resnonrel
  let cA: class A
  let cB: class B


  assert |- ( ( A \ `' `' A ) |` B ) = (/)

  proof
    cA
    cA
    ccnv
    ccnv
    cdif
    #
    cB
    cres
    #
    c0
    wss
    @1
    c0
    wceq
    @1
    @0
    cvv
    cres
    #
    c0
    cB
    cvv
    wss
    @1
    @2
    wss
    cB
    ssv
    cB
    cvv
    @0
    ssres2
    ax-mp
    @0
    ccnv
    #
    ccnv
    c0
    ccnv
    @2
    c0
    @3
    c0
    cA
    cnvnonrel
    cnveqi
    @0
    cnvcnv2
    cnv0
    3eqtr3i
    sseqtri
    @1
    ss0b
    mpbi
end
