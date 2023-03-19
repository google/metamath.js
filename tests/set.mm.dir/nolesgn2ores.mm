include "csur.mm"
include "wcel.mm"
include "con0.mm"
include "w3a.mm"
include "cres.mm"
include "wceq.mm"
include "cfv.mm"
include "c2o.mm"
include "wa.mm"
include "cslt.mm"
include "wbr.mm"
include "wn.mm"
include "csuc.mm"
include "cdm.mm"
include "cv.mm"
include "wral.mm"
include "cin.mm"
include "dmres.mm"
include "wss.mm"
include "word.mm"
include "simp11.mm"
include "nodmord.mm"
include "syl.mm"
include "c0.mm"
include "ndmfv.mm"
include "wne.mm"
include "c1o.mm"
include "2on.mm"
include "elexi.mm"
include "prid2.mm"
include "nosgnn0i.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "neneqd.mm"
include "con4i.mm"
include "adantl.mm"
include "3ad2ant2.mm"
include "ordsucss.mm"
include "sylc.mm"
include "df-ss.mm"
include "sylib.mm"
include "syl5eq.mm"
include "simp12.mm"
include "nolesgn2o.mm"
include "eqtr4d.mm"
include "eleq2d.mm"
include "wo.mm"
include "vex.mm"
include "elsuc.mm"
include "simp2l.mm"
include "fveq1d.mm"
include "adantr.mm"
include "simpr.mm"
include "fvresd.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "simp2r.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "syl5bi.mm"
include "imp.mm"
include "3eqtr4d.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "wfun.mm"
include "wb.mm"
include "nofun.mm"
include "funres.mm"
include "3syl.mm"
include "eqfunfv.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem nolesgn2ores
  let cA: class A
  let cB: class B
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. No /\ B e. No /\ X e. On ) /\ ( ( A |` X ) = ( B |` X ) /\ ( A ` X ) = 2o ) /\ -. B <s A ) -> ( A |` suc X ) = ( B |` suc X ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    cX
    con0
    wcel
    #
    w3a
    #
    cA
    cX
    cres
    #
    cB
    cX
    cres
    #
    wceq
    #
    cX
    cA
    cfv
    #
    c2o
    wceq
    #
    wa
    #
    cB
    cA
    cslt
    wbr
    wn
    #
    w3a
    #
    cA
    cX
    csuc
    #
    cres
    #
    cB
    @12
    cres
    #
    wceq
    #
    @13
    cdm
    #
    @14
    cdm
    #
    wceq
    #
    vx
    cv
    #
    @13
    cfv
    #
    @19
    @14
    cfv
    #
    wceq
    #
    vx
    @16
    wral
    #
    @11
    @16
    @12
    @17
    @11
    @16
    @12
    cA
    cdm
    #
    cin
    #
    @12
    cA
    @12
    dmres
    @11
    @12
    @24
    wss
    #
    @25
    @12
    wceq
    @11
    @24
    word
    #
    cX
    @24
    wcel
    #
    @26
    @11
    @0
    @27
    @0
    @1
    @2
    @9
    @10
    simp11
    #
    cA
    nodmord
    syl
    @9
    @3
    @28
    @10
    @8
    @28
    @6
    @28
    @8
    @28
    wn
    @7
    c0
    wceq
    #
    @8
    wn
    cX
    cA
    ndmfv
    @30
    @7
    c2o
    @30
    @7
    c2o
    wne
    c0
    c2o
    wne
    #
    c2o
    c1o
    c2o
    c2o
    con0
    2on
    elexi
    prid2
    nosgnn0i
    #
    @7
    c0
    c2o
    neeq1
    mpbiri
    neneqd
    syl
    con4i
    adantl
    3ad2ant2
    cX
    @24
    ordsucss
    sylc
    @12
    @24
    df-ss
    sylib
    syl5eq
    #
    @11
    @17
    @12
    cB
    cdm
    #
    cin
    #
    @12
    cB
    @12
    dmres
    @11
    @12
    @34
    wss
    #
    @35
    @12
    wceq
    @11
    @34
    word
    #
    cX
    @34
    wcel
    #
    @36
    @11
    @1
    @37
    @0
    @1
    @2
    @9
    @10
    simp12
    #
    cB
    nodmord
    syl
    @11
    cX
    cB
    cfv
    #
    c2o
    wceq
    #
    @38
    cA
    cB
    cX
    nolesgn2o
    #
    @38
    @41
    @38
    wn
    @40
    c0
    wceq
    #
    @41
    wn
    cX
    cB
    ndmfv
    @43
    @40
    c2o
    @43
    @40
    c2o
    wne
    @31
    @32
    @40
    c0
    c2o
    neeq1
    mpbiri
    neneqd
    syl
    con4i
    syl
    cX
    @34
    ordsucss
    sylc
    @12
    @34
    df-ss
    sylib
    syl5eq
    eqtr4d
    @11
    @22
    vx
    @16
    @11
    @19
    @16
    wcel
    @19
    @12
    wcel
    #
    @22
    @11
    @16
    @12
    @19
    @33
    eleq2d
    @11
    @44
    @22
    @11
    @44
    wa
    #
    @19
    cA
    cfv
    #
    @19
    cB
    cfv
    #
    @20
    @21
    @11
    @44
    @46
    @47
    wceq
    #
    @44
    @19
    cX
    wcel
    #
    @19
    cX
    wceq
    #
    wo
    @11
    @48
    @19
    cX
    vx
    vex
    elsuc
    @11
    @49
    @48
    @50
    @11
    @49
    @48
    @11
    @49
    wa
    #
    @19
    @4
    cfv
    #
    @19
    @5
    cfv
    #
    @46
    @47
    @11
    @52
    @53
    wceq
    @49
    @11
    @19
    @4
    @5
    @3
    @6
    @8
    @10
    simp2l
    fveq1d
    adantr
    @51
    @19
    cX
    cA
    @11
    @49
    simpr
    #
    fvresd
    @51
    @19
    cX
    cB
    @54
    fvresd
    3eqtr3d
    ex
    @11
    @48
    @50
    @7
    @40
    wceq
    @11
    @7
    c2o
    @40
    @3
    @6
    @8
    @10
    simp2r
    @42
    eqtr4d
    @50
    @46
    @7
    @47
    @40
    @19
    cX
    cA
    fveq2
    @19
    cX
    cB
    fveq2
    eqeq12d
    syl5ibrcom
    jaod
    syl5bi
    imp
    @45
    @19
    @12
    cA
    @11
    @44
    simpr
    #
    fvresd
    @45
    @19
    @12
    cB
    @55
    fvresd
    3eqtr4d
    ex
    sylbid
    ralrimiv
    @11
    @13
    wfun
    #
    @14
    wfun
    #
    @15
    @18
    @23
    wa
    wb
    @11
    @0
    cA
    wfun
    @56
    @29
    cA
    nofun
    @12
    cA
    funres
    3syl
    @11
    @1
    cB
    wfun
    @57
    @39
    cB
    nofun
    @12
    cB
    funres
    3syl
    vx
    @13
    @14
    eqfunfv
    syl2anc
    mpbir2and
end
