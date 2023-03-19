include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "crdg.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "con0.mm"
include "wral.mm"
include "wi.mm"
include "csuc.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "rdgprc0.mm"
include "0ex.mm"
include "rdg0.mm"
include "syl6eqr.mm"
include "rdgsuc.mm"
include "syl5ibr.mm"
include "imim2d.mm"
include "wlim.mm"
include "r19.21v.mm"
include "cres.mm"
include "word.mm"
include "wss.mm"
include "wb.mm"
include "limord.mm"
include "ordsson.mm"
include "wfn.mm"
include "rdgfnon.mm"
include "fvreseq.mm"
include "mpanl12.mm"
include "3syl.mm"
include "cima.mm"
include "cuni.mm"
include "crn.mm"
include "rneq.mm"
include "df-ima.mm"
include "3eqtr4g.mm"
include "unieqd.mm"
include "vex.mm"
include "wa.mm"
include "rdglim.mm"
include "mpan.mm"
include "sylbird.mm"
include "syl5bi.mm"
include "tfinds.mm"
include "com12.mm"
include "ralrimiv.mm"
include "eqfnfv.mm"
include "mp2an.mm"
include "sylibr.mm"

theorem rdgprc
  let cF: class F
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. I e. _V -> rec ( F , I ) = rec ( F , (/) ) )

  proof
    cI
    cvv
    wcel
    wn
    #
    vx
    cv
    #
    cF
    cI
    crdg
    #
    cfv
    #
    @1
    cF
    c0
    crdg
    #
    cfv
    #
    wceq
    #
    vx
    con0
    wral
    #
    @2
    @4
    wceq
    #
    @0
    @6
    vx
    con0
    @1
    con0
    wcel
    @0
    @6
    @0
    vz
    cv
    #
    @2
    cfv
    #
    @9
    @4
    cfv
    #
    wceq
    #
    wi
    #
    @0
    c0
    @2
    cfv
    #
    c0
    @4
    cfv
    #
    wceq
    #
    wi
    @0
    vy
    cv
    #
    @2
    cfv
    #
    @17
    @4
    cfv
    #
    wceq
    #
    wi
    #
    @0
    @17
    csuc
    #
    @2
    cfv
    #
    @22
    @4
    cfv
    #
    wceq
    #
    wi
    @0
    @6
    wi
    vz
    vy
    @1
    @9
    c0
    wceq
    #
    @12
    @16
    @0
    @26
    @10
    @14
    @11
    @15
    @9
    c0
    @2
    fveq2
    @9
    c0
    @4
    fveq2
    eqeq12d
    imbi2d
    vz
    vy
    weq
    #
    @12
    @20
    @0
    @27
    @10
    @18
    @11
    @19
    @9
    @17
    @2
    fveq2
    @9
    @17
    @4
    fveq2
    eqeq12d
    imbi2d
    @9
    @22
    wceq
    #
    @12
    @25
    @0
    @28
    @10
    @23
    @11
    @24
    @9
    @22
    @2
    fveq2
    @9
    @22
    @4
    fveq2
    eqeq12d
    imbi2d
    vz
    vx
    weq
    #
    @12
    @6
    @0
    @29
    @10
    @3
    @11
    @5
    @9
    @1
    @2
    fveq2
    @9
    @1
    @4
    fveq2
    eqeq12d
    imbi2d
    @0
    @14
    c0
    @15
    cF
    cI
    rdgprc0
    c0
    cF
    0ex
    rdg0
    syl6eqr
    @17
    con0
    wcel
    #
    @20
    @25
    @0
    @20
    @25
    @30
    @18
    cF
    cfv
    #
    @19
    cF
    cfv
    #
    wceq
    @18
    @19
    cF
    fveq2
    @30
    @23
    @31
    @24
    @32
    cI
    @17
    cF
    rdgsuc
    c0
    @17
    cF
    rdgsuc
    eqeq12d
    syl5ibr
    imim2d
    @21
    vy
    @9
    wral
    @0
    @20
    vy
    @9
    wral
    #
    wi
    @9
    wlim
    #
    @13
    @0
    @20
    vy
    @9
    r19.21v
    @34
    @33
    @12
    @0
    @34
    @33
    @2
    @9
    cres
    #
    @4
    @9
    cres
    #
    wceq
    #
    @12
    @34
    @9
    word
    @9
    con0
    wss
    #
    @37
    @33
    wb
    #
    @9
    limord
    @9
    ordsson
    @2
    con0
    wfn
    #
    @4
    con0
    wfn
    #
    @38
    @39
    cI
    cF
    rdgfnon
    #
    c0
    cF
    rdgfnon
    #
    vy
    con0
    @9
    @2
    @4
    fvreseq
    mpanl12
    3syl
    @37
    @12
    @34
    @2
    @9
    cima
    #
    cuni
    #
    @4
    @9
    cima
    #
    cuni
    #
    wceq
    #
    @37
    @44
    @46
    @37
    @35
    crn
    @36
    crn
    @44
    @46
    @35
    @36
    rneq
    @2
    @9
    df-ima
    @4
    @9
    df-ima
    3eqtr4g
    unieqd
    @9
    cvv
    wcel
    #
    @34
    @12
    @48
    wb
    vz
    vex
    @49
    @34
    wa
    @10
    @45
    @11
    @47
    cI
    @9
    cvv
    cF
    rdglim
    c0
    @9
    cvv
    cF
    rdglim
    eqeq12d
    mpan
    syl5ibr
    sylbird
    imim2d
    syl5bi
    tfinds
    com12
    ralrimiv
    @40
    @41
    @8
    @7
    wb
    @42
    @43
    vx
    con0
    @2
    @4
    eqfnfv
    mp2an
    sylibr
end
