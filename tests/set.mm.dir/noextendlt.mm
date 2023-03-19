include "csur.mm"
include "wcel.mm"
include "cdm.mm"
include "c1o.mm"
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
include "c0.mm"
include "c2o.mm"
include "ctp.mm"
include "wceq.mm"
include "wa.mm"
include "w3o.mm"
include "wfn.mm"
include "cin.mm"
include "wfun.mm"
include "nofun.mm"
include "funfn.mm"
include "sylib.mm"
include "nodmon.mm"
include "1on.mm"
include "fnsng.mm"
include "sylancl.mm"
include "wn.mm"
include "word.mm"
include "nodmord.mm"
include "ordirr.mm"
include "syl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "snidg.mm"
include "fvun2.mm"
include "syl112anc.mm"
include "fvsng.mm"
include "eqtrd.mm"
include "ndmfv.mm"
include "jca.mm"
include "3mix1d.mm"
include "fvex.mm"
include "brtp.mm"
include "necom.mm"
include "rabbii.mm"
include "inteqi.mm"
include "elexi.mm"
include "prid1.mm"
include "noextenddif.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "3brtr4d.mm"
include "wb.mm"
include "noextend.mm"
include "sltval2.mm"
include "mpancom.mm"
include "mpbird.mm"

theorem noextendlt
  let cA: class A
  let vx: setvar x


  assert |- ( A e. No -> ( A u. { <. dom A , 1o >. } ) <s A )

  proof
    cA
    csur
    wcel
    #
    cA
    cA
    cdm
    #
    c1o
    cop
    csn
    #
    cun
    #
    cA
    cslt
    wbr
    #
    vx
    cv
    #
    @3
    cfv
    #
    @5
    cA
    cfv
    #
    wne
    #
    vx
    con0
    crab
    #
    cint
    #
    @3
    cfv
    #
    @10
    cA
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
    @3
    cfv
    #
    @1
    cA
    cfv
    #
    @11
    @12
    @13
    @0
    @15
    c1o
    wceq
    #
    @16
    c0
    wceq
    #
    wa
    #
    @17
    @16
    c2o
    wceq
    #
    wa
    #
    @15
    c0
    wceq
    @20
    wa
    #
    w3o
    @15
    @16
    @13
    wbr
    @0
    @19
    @21
    @22
    @0
    @17
    @18
    @0
    @15
    @1
    @2
    cfv
    #
    c1o
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
    @25
    cin
    c0
    wceq
    #
    @1
    @25
    wcel
    #
    @15
    @23
    wceq
    @0
    cA
    wfun
    @24
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
    c1o
    con0
    wcel
    #
    @26
    cA
    nodmon
    #
    1on
    @1
    c1o
    con0
    con0
    fnsng
    sylancl
    @0
    @1
    @1
    wcel
    wn
    #
    @27
    @0
    @1
    word
    @32
    cA
    nodmord
    @1
    ordirr
    syl
    #
    @1
    @1
    disjsn
    sylibr
    @0
    @29
    @28
    @31
    @1
    con0
    snidg
    syl
    @1
    @25
    cA
    @2
    @1
    fvun2
    syl112anc
    @0
    @29
    @30
    @23
    c1o
    wceq
    @31
    1on
    @1
    c1o
    con0
    con0
    fvsng
    sylancl
    eqtrd
    @0
    @32
    @18
    @33
    @1
    cA
    ndmfv
    syl
    jca
    3mix1d
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @15
    @16
    @1
    @3
    fvex
    @1
    cA
    fvex
    brtp
    sylibr
    @0
    @10
    @1
    @3
    @0
    @10
    @7
    @6
    wne
    #
    vx
    con0
    crab
    #
    cint
    @1
    @9
    @35
    @8
    @34
    vx
    con0
    @6
    @7
    necom
    rabbii
    inteqi
    vx
    cA
    c1o
    c1o
    c2o
    c1o
    con0
    1on
    elexi
    prid1
    #
    noextenddif
    syl5eq
    #
    fveq2d
    @0
    @10
    @1
    cA
    @37
    fveq2d
    3brtr4d
    @3
    csur
    wcel
    @0
    @4
    @14
    wb
    cA
    c1o
    @36
    noextend
    @3
    cA
    vx
    sltval2
    mpancom
    mpbird
end
