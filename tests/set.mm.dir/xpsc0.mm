include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "cfv.mm"
include "cxp.mm"
include "c1o.mm"
include "cun.mm"
include "xpsc.mm"
include "fveq1i.mm"
include "wfn.mm"
include "cdm.mm"
include "cin.mm"
include "wceq.mm"
include "fnconstg.mm"
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
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "fvex.mm"
include "xpsn.mm"
include "sseqtri.mm"
include "funsn.mm"
include "funss.mm"
include "mp2.mm"
include "funfn.mm"
include "mpbi.mm"
include "a1i.mm"
include "dmxpss.mm"
include "sslin.mm"
include "wne.mm"
include "1n0.mm"
include "necomi.mm"
include "disjsn2.mm"
include "sseq0.mm"
include "mp2an.mm"
include "0ex.mm"
include "snid.mm"
include "fvun1.mm"
include "syl112anc.mm"
include "syl5eq.mm"
include "wa.mm"
include "xpsng.mm"
include "fveq1d.mm"
include "fvsng.mm"
include "eqtrd.mm"
include "mpan.mm"

theorem xpsc0
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( `' ( { A } +c { B } ) ` (/) ) = A )

  proof
    cA
    cV
    wcel
    #
    c0
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
    c0
    c0
    csn
    #
    @1
    cxp
    #
    cfv
    #
    cA
    @0
    @4
    c0
    @6
    c1o
    csn
    #
    @2
    cxp
    #
    cun
    #
    cfv
    #
    @7
    c0
    @3
    @10
    cA
    cB
    xpsc
    fveq1i
    @0
    @6
    @5
    wfn
    @9
    @9
    cdm
    #
    wfn
    #
    @5
    @12
    cin
    #
    c0
    wceq
    #
    c0
    @5
    wcel
    #
    @11
    @7
    wceq
    @5
    cA
    cV
    fnconstg
    @13
    @0
    @9
    wfun
    #
    @13
    @9
    c1o
    cB
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
    @2
    @20
    wss
    @9
    @21
    wss
    vx
    @2
    @20
    vx
    cv
    #
    @2
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
    cB
    cid
    @22
    cB
    elsni
    fveq2d
    syl5eqr
    vx
    @18
    velsn
    sylibr
    ssriv
    @2
    @20
    @8
    xpss2
    ax-mp
    c1o
    @18
    c1o
    con0
    1on
    elexi
    #
    cB
    cid
    fvex
    #
    xpsn
    sseqtri
    c1o
    @18
    @25
    @26
    funsn
    @9
    @19
    funss
    mp2
    @9
    funfn
    mpbi
    a1i
    @15
    @0
    @14
    @5
    @8
    cin
    #
    wss
    #
    @27
    c0
    wceq
    #
    @15
    @12
    @8
    wss
    @28
    @8
    @2
    dmxpss
    @12
    @8
    @5
    sslin
    ax-mp
    c0
    c1o
    wne
    @29
    c1o
    c0
    1n0
    necomi
    c0
    c1o
    disjsn2
    ax-mp
    @14
    @27
    sseq0
    mp2an
    a1i
    @16
    @0
    c0
    0ex
    snid
    a1i
    @5
    @12
    @6
    @9
    c0
    fvun1
    syl112anc
    syl5eq
    c0
    cvv
    wcel
    #
    @0
    @7
    cA
    wceq
    0ex
    @30
    @0
    wa
    #
    @7
    c0
    c0
    cA
    cop
    csn
    #
    cfv
    cA
    @31
    c0
    @6
    @32
    c0
    cA
    cvv
    cV
    xpsng
    fveq1d
    c0
    cA
    cvv
    cV
    fvsng
    eqtrd
    mpan
    eqtrd
end
