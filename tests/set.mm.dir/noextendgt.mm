include "csur.mm"
include "wcel.mm"
include "cdm.mm"
include "c2o.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cslt.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "c1o.mm"
include "c0.mm"
include "ctp.mm"
include "wceq.mm"
include "wa.mm"
include "w3o.mm"
include "wn.mm"
include "word.mm"
include "nodmord.mm"
include "ordirr.mm"
include "syl.mm"
include "ndmfv.mm"
include "wfn.mm"
include "cin.mm"
include "wfun.mm"
include "nofun.mm"
include "funfn.mm"
include "sylib.mm"
include "nodmon.mm"
include "2on.mm"
include "fnsng.mm"
include "sylancl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "snidg.mm"
include "fvun2.mm"
include "syl112anc.mm"
include "fvsng.mm"
include "eqtrd.mm"
include "jca.mm"
include "3mix3d.mm"
include "fvex.mm"
include "brtp.mm"
include "elexi.mm"
include "prid2.mm"
include "noextenddif.mm"
include "fveq2d.mm"
include "3brtr4d.mm"
include "wb.mm"
include "noextend.mm"
include "sltval2.mm"
include "mpdan.mm"
include "mpbird.mm"

theorem noextendgt
  let cA: class A
  let vx: setvar x


  assert |- ( A e. No -> A <s ( A u. { <. dom A , 2o >. } ) )

  proof
    cA
    csur
    wcel
    #
    cA
    cA
    cA
    cdm
    #
    c2o
    cop
    csn
    #
    cun
    #
    cslt
    wbr
    #
    vx
    cv
    #
    cA
    cfv
    @5
    @3
    cfv
    wne
    vx
    con0
    crab
    cint
    #
    cA
    cfv
    #
    @6
    @3
    cfv
    #
    c1o
    c0
    cop
    c1o
    c2o
    cop
    c0
    c2o
    cop
    ctp
    #
    wbr
    #
    @0
    @1
    cA
    cfv
    #
    @1
    @3
    cfv
    #
    @7
    @8
    @9
    @0
    @11
    c1o
    wceq
    #
    @12
    c0
    wceq
    wa
    #
    @13
    @12
    c2o
    wceq
    #
    wa
    #
    @11
    c0
    wceq
    #
    @15
    wa
    #
    w3o
    @11
    @12
    @9
    wbr
    @0
    @18
    @14
    @16
    @0
    @17
    @15
    @0
    @1
    @1
    wcel
    wn
    #
    @17
    @0
    @1
    word
    @19
    cA
    nodmord
    @1
    ordirr
    syl
    #
    @1
    cA
    ndmfv
    syl
    @0
    @12
    @1
    @2
    cfv
    #
    c2o
    @0
    cA
    @1
    wfn
    #
    @2
    @1
    csn
    #
    wfn
    #
    @1
    @23
    cin
    c0
    wceq
    #
    @1
    @23
    wcel
    #
    @12
    @21
    wceq
    @0
    cA
    wfun
    @22
    cA
    nofun
    cA
    funfn
    sylib
    @0
    @1
    con0
    wcel
    #
    c2o
    con0
    wcel
    #
    @24
    cA
    nodmon
    #
    2on
    @1
    c2o
    con0
    con0
    fnsng
    sylancl
    @0
    @19
    @25
    @20
    @1
    @1
    disjsn
    sylibr
    @0
    @27
    @26
    @29
    @1
    con0
    snidg
    syl
    @1
    @23
    cA
    @2
    @1
    fvun2
    syl112anc
    @0
    @27
    @28
    @21
    c2o
    wceq
    @29
    2on
    @1
    c2o
    con0
    con0
    fvsng
    sylancl
    eqtrd
    jca
    3mix3d
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @11
    @12
    @1
    cA
    fvex
    @1
    @3
    fvex
    brtp
    sylibr
    @0
    @6
    @1
    cA
    vx
    cA
    c2o
    c1o
    c2o
    c2o
    con0
    2on
    elexi
    prid2
    #
    noextenddif
    #
    fveq2d
    @0
    @6
    @1
    @3
    @31
    fveq2d
    3brtr4d
    @0
    @3
    csur
    wcel
    @4
    @10
    wb
    cA
    c2o
    @30
    noextend
    cA
    @3
    vx
    sltval2
    mpdan
    mpbird
end
