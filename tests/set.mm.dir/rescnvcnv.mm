include "ccnv.mm"
include "cres.mm"
include "cvv.mm"
include "cin.mm"
include "cnvcnv2.mm"
include "reseq1i.mm"
include "resres.mm"
include "wss.mm"
include "wceq.mm"
include "ssv.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "reseq2i.mm"
include "3eqtri.mm"

theorem rescnvcnv
  let cA: class A
  let cB: class B


  assert |- ( `' `' A |` B ) = ( A |` B )

  proof
    cA
    ccnv
    ccnv
    #
    cB
    cres
    cA
    cvv
    cres
    #
    cB
    cres
    cA
    cvv
    cB
    cin
    #
    cres
    cA
    cB
    cres
    @0
    @1
    cB
    cA
    cnvcnv2
    reseq1i
    cA
    cvv
    cB
    resres
    @2
    cB
    cA
    cB
    cvv
    wss
    @2
    cB
    wceq
    cB
    ssv
    cB
    cvv
    sseqin2
    mpbi
    reseq2i
    3eqtri
end
