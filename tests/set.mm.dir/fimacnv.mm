include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "crn.mm"
include "imassrn.mm"
include "cdm.mm"
include "dfdm4.mm"
include "fdm.mm"
include "ssid.mm"
include "syl6eqss.mm"
include "syl5eqssr.mm"
include "syl5ss.mm"
include "wss.mm"
include "frn.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "syl5sseqr.mm"
include "funimass3.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqssd.mm"

theorem fimacnv
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B -> ( `' F " B ) = A )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    ccnv
    #
    cB
    cima
    #
    cA
    @0
    @2
    @1
    crn
    #
    cA
    @1
    cB
    imassrn
    @0
    @3
    cF
    cdm
    #
    cA
    cF
    dfdm4
    @0
    @4
    cA
    cA
    cA
    cB
    cF
    fdm
    #
    cA
    ssid
    #
    syl6eqss
    syl5eqssr
    syl5ss
    @0
    cF
    cA
    cima
    #
    cB
    wss
    #
    cA
    @2
    wss
    #
    @0
    @7
    cF
    crn
    cB
    cF
    cA
    imassrn
    cA
    cB
    cF
    frn
    syl5ss
    @0
    cF
    wfun
    cA
    @4
    wss
    @8
    @9
    wb
    cA
    cB
    cF
    ffun
    @0
    cA
    cA
    @4
    @6
    @5
    syl5sseqr
    cA
    cB
    cF
    funimass3
    syl2anc
    mpbid
    eqssd
end
