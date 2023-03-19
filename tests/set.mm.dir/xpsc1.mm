include "wcel.mm"
include "c1o.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cfv.mm"
include "cxp.mm"
include "c0.mm"
include "cun.mm"
include "xpsc.mm"
include "fveq1i.mm"
include "cdm.mm"
include "wfn.mm"
include "cin.mm"
include "wceq.mm"
include "wfun.mm"
include "cid.mm"
include "cop.mm"
include "wss.mm"
include "cv.mm"
include "cvv.mm"
include "vex.mm"
include "fvi.mm"
include "ax-mp.mm"
include "elsni.mm"
include "fveq2d.mm"
include "syl5eqr.mm"
include "velsn.mm"
include "sylibr.mm"
include "ssriv.mm"
include "xpss2.mm"
include "0ex.mm"
include "fvex.mm"
include "xpsn.mm"
include "sseqtri.mm"
include "funsn.mm"
include "funss.mm"
include "mp2.mm"
include "funfn.mm"
include "mpbi.mm"
include "a1i.mm"
include "fnconstg.mm"
include "dmxpss.mm"
include "ssrin.mm"
include "wne.mm"
include "1n0.mm"
include "necomi.mm"
include "disjsn2.mm"
include "sseq0.mm"
include "mp2an.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "snid.mm"
include "fvun2.mm"
include "syl112anc.mm"
include "syl5eq.mm"
include "wa.mm"
include "xpsng.mm"
include "fveq1d.mm"
include "fvsng.mm"
include "eqtrd.mm"
include "mpan.mm"

theorem xpsc1
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( B e. V -> ( `' ( { A } +c { B } ) ` 1o ) = B )

  proof
    cB
    cV
    wcel
    #
    c1o
    cA
    csn
    #
    cB
    csn
    #
    ccda
    co
    ccnv
    #
    cfv
    #
    c1o
    c1o
    csn
    #
    @2
    cxp
    #
    cfv
    #
    cB
    @0
    @4
    c1o
    c0
    csn
    #
    @1
    cxp
    #
    @6
    cun
    #
    cfv
    #
    @7
    c1o
    @3
    @10
    cA
    cB
    xpsc
    fveq1i
    @0
    @9
    @9
    cdm
    #
    wfn
    #
    @6
    @5
    wfn
    @12
    @5
    cin
    #
    c0
    wceq
    #
    c1o
    @5
    wcel
    #
    @11
    @7
    wceq
    @13
    @0
    @9
    wfun
    #
    @13
    @9
    c0
    cA
    cid
    cfv
    #
    cop
    csn
    #
    wss
    @19
    wfun
    @17
    @9
    @8
    @18
    csn
    #
    cxp
    #
    @19
    @1
    @20
    wss
    @9
    @21
    wss
    vx
    @1
    @20
    vx
    cv
    #
    @1
    wcel
    #
    @22
    @18
    wceq
    @22
    @20
    wcel
    @23
    @22
    @22
    cid
    cfv
    #
    @18
    @22
    cvv
    wcel
    @24
    @22
    wceq
    vx
    vex
    @22
    cvv
    fvi
    ax-mp
    @23
    @22
    cA
    cid
    @22
    cA
    elsni
    fveq2d
    syl5eqr
    vx
    @18
    velsn
    sylibr
    ssriv
    @1
    @20
    @8
    xpss2
    ax-mp
    c0
    @18
    0ex
    cA
    cid
    fvex
    #
    xpsn
    sseqtri
    c0
    @18
    0ex
    @25
    funsn
    @9
    @19
    funss
    mp2
    @9
    funfn
    mpbi
    a1i
    @5
    cB
    cV
    fnconstg
    @15
    @0
    @14
    @8
    @5
    cin
    #
    wss
    #
    @26
    c0
    wceq
    #
    @15
    @12
    @8
    wss
    @27
    @8
    @1
    dmxpss
    @12
    @8
    @5
    ssrin
    ax-mp
    c0
    c1o
    wne
    @28
    c1o
    c0
    1n0
    necomi
    c0
    c1o
    disjsn2
    ax-mp
    @14
    @26
    sseq0
    mp2an
    a1i
    @16
    @0
    c1o
    c1o
    con0
    1on
    elexi
    snid
    a1i
    @12
    @5
    @9
    @6
    c1o
    fvun2
    syl112anc
    syl5eq
    c1o
    con0
    wcel
    #
    @0
    @7
    cB
    wceq
    1on
    @29
    @0
    wa
    #
    @7
    c1o
    c1o
    cB
    cop
    csn
    #
    cfv
    cB
    @30
    c1o
    @6
    @31
    c1o
    cB
    con0
    cV
    xpsng
    fveq1d
    c1o
    cB
    con0
    cV
    fvsng
    eqtrd
    mpan
    eqtrd
end
