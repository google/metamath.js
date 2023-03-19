include "c0.mm"
include "cesum.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cc0.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "csn.mm"
include "wceq.mm"
include "wtru.mm"
include "cvv.mm"
include "nftru.mm"
include "nfcv.mm"
include "wcel.mm"
include "0ex.mm"
include "a1i.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wral.mm"
include "ral0.mm"
include "r19.21bi.mm"
include "cv.mm"
include "cxrs.mm"
include "cress.mm"
include "cgsu.mm"
include "pw0.mm"
include "ineq1i.mm"
include "0fin.mm"
include "wss.mm"
include "snssi.mm"
include "df-ss.mm"
include "sylib.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "velsn.mm"
include "sylbb.mm"
include "mpteq1d.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "xrge00.mm"
include "gsum0.mm"
include "adantl.mm"
include "esumval.mm"
include "trud.mm"
include "cxp.mm"
include "fconstmpt.mm"
include "eqcomi.mm"
include "wfn.mm"
include "wne.mm"
include "wb.mm"
include "0xr.mm"
include "rgenw.mm"
include "eqid.mm"
include "fnmpt.mm"
include "snnz.mm"
include "eqnetri.mm"
include "fconst5.mm"
include "mp2an.mm"
include "mpbi.mm"
include "supeq1i.mm"
include "wor.mm"
include "xrltso.mm"
include "supsn.mm"
include "3eqtri.mm"

theorem esumnul
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- sum* x e. (/) A = 0

  proof
    c0
    cA
    vx
    cesum
    #
    vy
    c0
    cpw
    #
    cfn
    cin
    #
    cc0
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cc0
    csn
    #
    cxr
    clt
    csup
    #
    cc0
    @0
    @5
    wceq
    wtru
    vy
    c0
    cA
    cc0
    vx
    cvv
    vx
    nftru
    vx
    c0
    nfcv
    c0
    cvv
    wcel
    wtru
    0ex
    a1i
    wtru
    cA
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    vx
    c0
    @9
    vx
    c0
    wral
    wtru
    @9
    vx
    ral0
    a1i
    r19.21bi
    vy
    cv
    #
    @2
    wcel
    #
    cxrs
    @8
    cress
    co
    #
    vx
    @10
    cA
    cmpt
    #
    cgsu
    co
    #
    cc0
    wceq
    wtru
    @11
    @14
    @12
    c0
    cgsu
    co
    cc0
    @11
    @13
    c0
    @12
    cgsu
    @11
    @13
    vx
    c0
    cA
    cmpt
    c0
    @11
    vx
    @10
    c0
    cA
    @11
    @10
    c0
    csn
    #
    wcel
    @10
    c0
    wceq
    @2
    @15
    @10
    @2
    @15
    cfn
    cin
    #
    @15
    @1
    @15
    cfn
    pw0
    ineq1i
    c0
    cfn
    wcel
    #
    @16
    @15
    wceq
    #
    0fin
    @17
    @15
    cfn
    wss
    @18
    c0
    cfn
    snssi
    @15
    cfn
    df-ss
    sylib
    ax-mp
    eqtri
    #
    eleq2i
    vy
    c0
    velsn
    sylbb
    mpteq1d
    vx
    cA
    mpt0
    syl6eq
    oveq2d
    @12
    cc0
    xrge00
    gsum0
    syl6eq
    adantl
    esumval
    trud
    cxr
    @4
    @6
    clt
    @3
    @2
    @6
    cxp
    #
    wceq
    #
    @4
    @6
    wceq
    #
    @20
    @3
    vy
    @2
    cc0
    fconstmpt
    eqcomi
    @3
    @2
    wfn
    #
    @2
    c0
    wne
    @21
    @22
    wb
    cc0
    cxr
    wcel
    #
    vy
    @2
    wral
    @23
    @24
    vy
    @2
    0xr
    rgenw
    vy
    @2
    cc0
    @3
    cxr
    @3
    eqid
    fnmpt
    ax-mp
    @2
    @15
    c0
    @19
    c0
    0ex
    snnz
    eqnetri
    @2
    cc0
    @3
    fconst5
    mp2an
    mpbi
    supeq1i
    cxr
    clt
    wor
    @24
    @7
    cc0
    wceq
    xrltso
    0xr
    cxr
    cc0
    clt
    supsn
    mp2an
    3eqtri
end
