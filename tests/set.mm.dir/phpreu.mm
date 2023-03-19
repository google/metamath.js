include "cfn.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wrmo.mm"
include "wreu.mm"
include "crab.mm"
include "cmpt.mm"
include "wf1.mm"
include "wmo.mm"
include "wal.mm"
include "wf1o.mm"
include "wfo.mm"
include "wf.mm"
include "wi.mm"
include "eleq1.mm"
include "biimpac.mm"
include "rabid.mm"
include "simplbi2com.mm"
include "syl.mm"
include "impancom.mm"
include "ancrd.mm"
include "expimpd.mm"
include "reximdv2.mm"
include "ralimia.mm"
include "wb.mm"
include "simplbi.mm"
include "pm4.71rd.mm"
include "copab.mm"
include "cop.mm"
include "df-mpt.mm"
include "breqi.mm"
include "df-br.mm"
include "opabid.mm"
include "3bitri.mm"
include "syl6bbr.mm"
include "sylan2.mm"
include "rexbidva.mm"
include "ralbiia.mm"
include "weq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfmpt1.mm"
include "nfbr.mm"
include "nfv.mm"
include "breq1.mm"
include "cbvrexf.mm"
include "syl6bb.mm"
include "cbvralv.mm"
include "bitr4i.mm"
include "sylib.mm"
include "csb.mm"
include "nfcri.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "nfan.mm"
include "csbeq1a.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvopab1.mm"
include "3eqtr4i.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "elrabf.mm"
include "simprbi.mm"
include "fmpti.mm"
include "jctil.mm"
include "dffo4.mm"
include "sylibr.mm"
include "adantl.mm"
include "cdom.mm"
include "cvv.mm"
include "wss.mm"
include "relen.mm"
include "brrelex2i.mm"
include "ssrab2.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "ensym.mm"
include "domentr.mm"
include "syl2anc.mm"
include "ad2antlr.mm"
include "enfi.mm"
include "rabfi.mm"
include "fodomfi.mm"
include "syl2an.mm"
include "sbth.mm"
include "simpll.mm"
include "fofinf1o.mm"
include "syl3anc.mm"
include "f1of1.mm"
include "dff12.mm"
include "mobidv.mm"
include "cbvmo.mm"
include "cbvalv.mm"
include "mormo.mm"
include "alimi.mm"
include "alral.mm"
include "4syl.mm"
include "rmobidva.mm"
include "ex.mm"
include "pm4.71d.mm"
include "reu5.mm"
include "ralbii.mm"
include "r19.26.mm"
include "bitri.mm"

theorem phpreu
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vb: setvar b

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  assert |- ( ( A e. Fin /\ A ~~ B ) -> ( A. x e. A E. y e. B x = C <-> A. x e. A E! y e. B x = C ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    cB
    cen
    wbr
    #
    wa
    #
    vx
    cv
    #
    cC
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    @6
    @4
    vy
    cB
    wrmo
    #
    vx
    cA
    wral
    #
    wa
    #
    @4
    vy
    cB
    wreu
    #
    vx
    cA
    wral
    #
    @2
    @6
    @8
    @2
    @6
    @8
    @2
    @6
    wa
    #
    vy
    cv
    #
    @3
    vy
    cC
    cA
    wcel
    #
    vy
    cB
    crab
    #
    cC
    cmpt
    #
    wbr
    #
    vy
    cB
    wrmo
    #
    vx
    cA
    wral
    #
    @8
    @12
    @15
    cA
    @16
    wf1
    #
    @17
    vy
    wmo
    #
    vx
    wal
    #
    @18
    vx
    wal
    @19
    @12
    @15
    cA
    @16
    wf1o
    #
    @20
    @12
    @15
    cA
    @16
    wfo
    #
    @15
    cA
    cen
    wbr
    #
    @0
    @23
    @6
    @24
    @2
    @6
    @15
    cA
    @16
    wf
    #
    vb
    cv
    #
    va
    cv
    #
    @16
    wbr
    #
    vb
    @15
    wrex
    #
    va
    cA
    wral
    #
    wa
    @24
    @6
    @31
    @26
    @6
    @4
    vy
    @15
    wrex
    #
    vx
    cA
    wral
    #
    @31
    @5
    @32
    vx
    cA
    @3
    cA
    wcel
    #
    @4
    @4
    vy
    cB
    @15
    @34
    @13
    cB
    wcel
    #
    @4
    @13
    @15
    wcel
    #
    @4
    wa
    #
    @34
    @35
    wa
    #
    @4
    @36
    @34
    @4
    @35
    @36
    @34
    @4
    wa
    @14
    @35
    @36
    wi
    @4
    @34
    @14
    @3
    cC
    cA
    eleq1
    biimpac
    @36
    @35
    @14
    @14
    vy
    cB
    rabid
    #
    simplbi2com
    syl
    impancom
    #
    ancrd
    expimpd
    reximdv2
    ralimia
    @33
    @17
    vy
    @15
    wrex
    #
    vx
    cA
    wral
    @31
    @32
    @41
    vx
    cA
    @34
    @4
    @17
    vy
    @15
    @36
    @34
    @35
    @4
    @17
    wb
    @36
    @35
    @14
    @39
    simplbi
    @38
    @4
    @37
    @17
    @38
    @4
    @36
    @40
    pm4.71rd
    @17
    @13
    @3
    @37
    vy
    vx
    copab
    #
    wbr
    @13
    @3
    cop
    @42
    wcel
    @37
    @13
    @3
    @16
    @42
    vy
    vx
    @15
    cC
    df-mpt
    #
    breqi
    @13
    @3
    @42
    df-br
    @37
    vy
    vx
    opabid
    3bitri
    syl6bbr
    #
    sylan2
    rexbidva
    ralbiia
    @30
    @41
    va
    vx
    cA
    va
    vx
    weq
    #
    @30
    @27
    @3
    @16
    wbr
    #
    vb
    @15
    wrex
    @41
    @45
    @29
    @46
    vb
    @15
    @28
    @3
    @27
    @16
    breq2
    #
    rexbidv
    @46
    @17
    vb
    vy
    @15
    vb
    @15
    nfcv
    @14
    vy
    cB
    nfrab1
    #
    vy
    @27
    @3
    @16
    vy
    @27
    nfcv
    #
    vy
    @15
    cC
    nfmpt1
    vy
    @3
    nfcv
    nfbr
    #
    @17
    vb
    nfv
    #
    @27
    @13
    @3
    @16
    breq1
    #
    cbvrexf
    syl6bb
    cbvralv
    bitr4i
    sylib
    vb
    @15
    cA
    vy
    @27
    cC
    csb
    #
    @16
    @42
    @27
    @15
    wcel
    #
    @3
    @53
    wceq
    #
    wa
    #
    vb
    vx
    copab
    @16
    vb
    @15
    @53
    cmpt
    @37
    @56
    vy
    vx
    vb
    @37
    vb
    nfv
    @54
    @55
    vy
    vy
    vb
    @15
    @48
    nfcri
    vy
    @3
    @53
    vy
    @27
    cC
    nfcsb1v
    #
    nfeq2
    nfan
    vy
    vb
    weq
    #
    @36
    @54
    @4
    @55
    @13
    @27
    @15
    eleq1
    @58
    cC
    @53
    @3
    vy
    @27
    cC
    csbeq1a
    #
    eqeq2d
    anbi12d
    cbvopab1
    @43
    vb
    vx
    @15
    @53
    df-mpt
    3eqtr4i
    @54
    @27
    cB
    wcel
    @53
    cA
    wcel
    #
    @14
    @60
    vy
    @27
    cB
    @49
    vy
    cB
    nfcv
    vy
    @53
    cA
    @57
    nfel1
    @58
    cC
    @53
    cA
    @59
    eleq1d
    elrabf
    simprbi
    fmpti
    jctil
    vb
    va
    @15
    cA
    @16
    dffo4
    sylibr
    #
    adantl
    @12
    @15
    cA
    cdom
    wbr
    #
    cA
    @15
    cdom
    wbr
    #
    @25
    @1
    @62
    @0
    @6
    @1
    @15
    cB
    cdom
    wbr
    #
    cB
    cA
    cen
    wbr
    @62
    @1
    cB
    cvv
    wcel
    @15
    cB
    wss
    @64
    cA
    cB
    cen
    relen
    brrelex2i
    @14
    vy
    cB
    ssrab2
    @15
    cB
    cvv
    ssdomg
    mpisyl
    cA
    cB
    ensym
    @15
    cB
    cA
    domentr
    syl2anc
    ad2antlr
    @2
    @15
    cfn
    wcel
    #
    @24
    @63
    @6
    @2
    cB
    cfn
    wcel
    #
    @65
    @1
    @0
    @66
    cA
    cB
    enfi
    biimpac
    @14
    vy
    cB
    rabfi
    syl
    @61
    @15
    cA
    @16
    fodomfi
    syl2an
    @15
    cA
    sbth
    syl2anc
    @0
    @1
    @6
    simpll
    @15
    cA
    @16
    fofinf1o
    syl3anc
    @15
    cA
    @16
    f1of1
    syl
    @20
    @29
    vb
    wmo
    #
    va
    wal
    #
    @22
    @20
    @26
    @68
    vb
    va
    @15
    cA
    @16
    dff12
    simprbi
    @67
    @21
    va
    vx
    @45
    @67
    @46
    vb
    wmo
    @21
    @45
    @29
    @46
    vb
    @47
    mobidv
    @46
    @17
    vb
    vy
    @50
    @51
    @52
    cbvmo
    syl6bb
    cbvalv
    sylib
    @21
    @18
    vx
    @17
    vy
    cB
    mormo
    alimi
    @18
    vx
    cA
    alral
    4syl
    @7
    @18
    vx
    cA
    @34
    @4
    @17
    vy
    cB
    @44
    rmobidva
    ralbiia
    sylibr
    ex
    pm4.71d
    @11
    @5
    @7
    wa
    #
    vx
    cA
    wral
    @9
    @10
    @69
    vx
    cA
    @4
    vy
    cB
    reu5
    ralbii
    @5
    @7
    vx
    cA
    r19.26
    bitri
    syl6bbr
end
