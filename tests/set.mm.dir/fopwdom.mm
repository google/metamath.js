include "wcel.mm"
include "wfo.mm"
include "wa.mm"
include "cpw.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cvv.mm"
include "wss.mm"
include "crn.mm"
include "imassrn.mm"
include "cdm.mm"
include "dfdm4.mm"
include "wf.mm"
include "wceq.mm"
include "fof.mm"
include "fdm.mm"
include "syl.mm"
include "syl5eqr.mm"
include "syl5sseq.mm"
include "adantl.mm"
include "wb.mm"
include "cnvexg.mm"
include "adantr.mm"
include "imaexg.mm"
include "elpwg.mm"
include "3syl.mm"
include "mpbird.mm"
include "a1d.mm"
include "weq.mm"
include "imaeq2.mm"
include "simpllr.mm"
include "simplrl.mm"
include "elpwid.mm"
include "foimacnv.mm"
include "syl2anc.mm"
include "simplrr.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "impbid1.mm"
include "rnexg.mm"
include "forn.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "pwexg.mm"
include "dmfex.mm"
include "sylan2.mm"
include "dom3d.mm"

theorem fopwdom
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b


  assert |- ( ( F e. V /\ F : A -onto-> B ) -> ~P B ~<_ ~P A )

  proof
    cF
    cV
    wcel
    #
    cA
    cB
    cF
    wfo
    #
    wa
    #
    va
    vb
    cB
    cpw
    #
    cA
    cpw
    #
    cF
    ccnv
    #
    va
    cv
    #
    cima
    #
    @5
    vb
    cv
    #
    cima
    #
    cvv
    cvv
    @2
    @7
    @4
    wcel
    #
    @6
    @3
    wcel
    #
    @2
    @10
    @7
    cA
    wss
    #
    @1
    @12
    @0
    @1
    @5
    crn
    #
    @7
    cA
    @5
    @6
    imassrn
    @1
    @13
    cF
    cdm
    #
    cA
    cF
    dfdm4
    @1
    cA
    cB
    cF
    wf
    #
    @14
    cA
    wceq
    cA
    cB
    cF
    fof
    #
    cA
    cB
    cF
    fdm
    syl
    syl5eqr
    syl5sseq
    adantl
    @2
    @5
    cvv
    wcel
    #
    @7
    cvv
    wcel
    @10
    @12
    wb
    @0
    @17
    @1
    cF
    cV
    cnvexg
    adantr
    @5
    @6
    cvv
    imaexg
    @7
    cA
    cvv
    elpwg
    3syl
    mpbird
    a1d
    @2
    @11
    @8
    @3
    wcel
    #
    wa
    #
    @7
    @9
    wceq
    #
    va
    vb
    weq
    #
    wb
    @2
    @19
    wa
    #
    @20
    @21
    @22
    @20
    @21
    @22
    @20
    wa
    #
    cF
    @7
    cima
    #
    cF
    @9
    cima
    #
    @6
    @8
    @20
    @24
    @25
    wceq
    @22
    @7
    @9
    cF
    imaeq2
    adantl
    @23
    @1
    @6
    cB
    wss
    @24
    @6
    wceq
    @0
    @1
    @19
    @20
    simpllr
    #
    @23
    @6
    cB
    @2
    @11
    @18
    @20
    simplrl
    elpwid
    cA
    cB
    @6
    cF
    foimacnv
    syl2anc
    @23
    @1
    @8
    cB
    wss
    @25
    @8
    wceq
    @26
    @23
    @8
    cB
    @2
    @11
    @18
    @20
    simplrr
    elpwid
    cA
    cB
    @8
    cF
    foimacnv
    syl2anc
    3eqtr3d
    ex
    @6
    @8
    @5
    imaeq2
    impbid1
    ex
    @2
    cB
    cvv
    wcel
    #
    @3
    cvv
    wcel
    @0
    @1
    @27
    @0
    cF
    crn
    #
    cvv
    wcel
    @1
    @27
    cF
    cV
    rnexg
    @1
    @28
    cB
    cvv
    cA
    cB
    cF
    forn
    eleq1d
    syl5ibcom
    imp
    cB
    cvv
    pwexg
    syl
    @2
    cA
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @1
    @0
    @15
    @29
    @16
    cA
    cB
    cV
    cF
    dmfex
    sylan2
    cA
    cvv
    pwexg
    syl
    dom3d
end
