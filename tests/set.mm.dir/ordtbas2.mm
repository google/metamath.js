include "ctsr.mm"
include "wcel.mm"
include "cun.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "w3o.mm"
include "cvv.mm"
include "wb.mm"
include "wss.mm"
include "ssun1.mm"
include "csn.mm"
include "ssun2.mm"
include "cuni.mm"
include "ordtuni.mm"
include "cdm.mm"
include "dmexg.mm"
include "syl5eqel.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "ssexg.mm"
include "sylancr.mm"
include "elfiun.mm"
include "syl2anc.mm"
include "ordtbaslem.mm"
include "syl6eqss.mm"
include "syl6ss.mm"
include "sseld.mm"
include "crn.mm"
include "ccnv.mm"
include "wbr.mm"
include "wn.mm"
include "crab.mm"
include "cmpt.mm"
include "cnvtsr.mm"
include "df-rn.mm"
include "eqid.mm"
include "syl.mm"
include "cps.mm"
include "tsrps.mm"
include "psrn.mm"
include "vex.mm"
include "brcnv.mm"
include "bicomi.mm"
include "notbii.mm"
include "a1i.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "wa.mm"
include "cmpt2.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "weq.mm"
include "breq2.mm"
include "notbid.mm"
include "rabbidv.mm"
include "cbvmptv.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "breq1.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "ineq12.mm"
include "inrab.mm"
include "reximi.mm"
include "sylbir.mm"
include "syl6bi.mm"
include "imp.mm"
include "inex1.mm"
include "elrnmpt2g.mm"
include "syl6eleqr.mm"
include "sseldi.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "3jaod.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "ssfii.mm"
include "cxp.mm"
include "wf.mm"
include "wral.mm"
include "adantr.mm"
include "simprl.mm"
include "eqidd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "rabexg.mm"
include "3syl.mm"
include "mpbird.mm"
include "sseldd.mm"
include "simprr.mm"
include "fiin.mm"
include "syl5eqelr.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "frn.mm"
include "syl5eqss.mm"
include "unssd.mm"
include "eqssd.mm"

theorem ordtbas2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cV: class V
  assume ordtval.1: |- X = dom R
  assume ordtval.2: |- A = ran ( x e. X |-> { y e. X | -. y R x } )
  assume ordtval.3: |- B = ran ( x e. X |-> { y e. X | -. x R y } )
  assume ordtval.4: |- C = ran ( a e. X , b e. X |-> { y e. X | ( -. y R a /\ -. b R y ) } )

  disjoint a b
  disjoint A a
  disjoint A b
  disjoint a x
  disjoint a y
  disjoint R a
  disjoint b x
  disjoint b y
  disjoint R b
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint X a
  disjoint X b
  disjoint X x
  disjoint X y
  disjoint B a
  disjoint B b
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a w
  disjoint a z
  disjoint b m
  disjoint b n
  disjoint b r
  disjoint b w
  disjoint b z
  disjoint m n
  disjoint m r
  disjoint m w
  disjoint m z
  disjoint A m
  disjoint n r
  disjoint n w
  disjoint n z
  disjoint A n
  disjoint r w
  disjoint r z
  disjoint A r
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint m x
  disjoint m y
  disjoint R m
  disjoint n x
  disjoint n y
  disjoint R n
  disjoint r x
  disjoint r y
  disjoint R r
  disjoint w x
  disjoint w y
  disjoint R w
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X w
  disjoint X z
  disjoint B m
  disjoint B n
  disjoint B r
  disjoint B z
  disjoint C m
  disjoint C n
  disjoint C z
  disjoint V x
  assert |- ( R e. TosetRel -> ( fi ` ( A u. B ) ) = ( ( A u. B ) u. C ) )

  proof
    cR
    ctsr
    wcel
    #
    cA
    cB
    cun
    #
    cfi
    cfv
    #
    @1
    cC
    cun
    #
    @0
    vz
    @2
    @3
    @0
    vz
    cv
    #
    @2
    wcel
    #
    @4
    cA
    cfi
    cfv
    #
    wcel
    #
    @4
    cB
    cfi
    cfv
    #
    wcel
    #
    @4
    vm
    cv
    #
    vn
    cv
    #
    cin
    #
    wceq
    #
    vn
    @8
    wrex
    vm
    @6
    wrex
    #
    w3o
    #
    @4
    @3
    wcel
    #
    @0
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @5
    @15
    wb
    @0
    cA
    @1
    wss
    @1
    cvv
    wcel
    #
    @17
    cA
    cB
    ssun1
    #
    @0
    @1
    cX
    csn
    #
    @1
    cun
    #
    wss
    @22
    cvv
    wcel
    #
    @19
    @1
    @21
    ssun2
    @0
    @22
    cuni
    #
    cvv
    wcel
    @23
    @0
    cX
    @24
    cvv
    vx
    vy
    cA
    cB
    cR
    ctsr
    cX
    ordtval.1
    ordtval.2
    ordtval.3
    ordtuni
    @0
    cX
    cR
    cdm
    cvv
    ordtval.1
    cR
    ctsr
    dmexg
    syl5eqel
    #
    eqeltrrd
    @22
    uniexb
    sylibr
    @1
    @22
    cvv
    ssexg
    sylancr
    #
    cA
    @1
    cvv
    ssexg
    sylancr
    @0
    cB
    @1
    wss
    @19
    @18
    cB
    cA
    ssun2
    #
    @26
    cB
    @1
    cvv
    ssexg
    sylancr
    vm
    vn
    @4
    cA
    cB
    cvv
    cvv
    elfiun
    syl2anc
    @0
    @7
    @16
    @9
    @14
    @0
    @6
    @3
    @4
    @0
    @6
    @1
    @3
    @0
    @6
    cA
    @1
    vx
    vy
    cA
    cR
    cX
    ordtval.1
    ordtval.2
    ordtbaslem
    #
    @20
    syl6eqss
    @1
    cC
    ssun1
    #
    syl6ss
    sseld
    @0
    @8
    @3
    @4
    @0
    @8
    @1
    @3
    @0
    @8
    cB
    @1
    @0
    vx
    cR
    crn
    #
    vy
    cv
    #
    vx
    cv
    #
    cR
    ccnv
    #
    wbr
    #
    wn
    #
    vy
    @30
    crab
    #
    cmpt
    #
    crn
    #
    cfi
    cfv
    #
    @38
    @8
    cB
    @0
    @33
    ctsr
    wcel
    @39
    @38
    wceq
    cR
    cnvtsr
    vx
    vy
    @38
    @33
    @30
    cR
    df-rn
    @38
    eqid
    ordtbaslem
    syl
    @0
    cB
    @38
    cfi
    @0
    cB
    vx
    cX
    @32
    @31
    cR
    wbr
    #
    wn
    #
    vy
    cX
    crab
    #
    cmpt
    #
    crn
    #
    @38
    ordtval.3
    @0
    @43
    @37
    @0
    vx
    cX
    @42
    @30
    @36
    @0
    cR
    cps
    wcel
    cX
    @30
    wceq
    cR
    tsrps
    cR
    cX
    ordtval.1
    psrn
    syl
    #
    @0
    @41
    @35
    vy
    cX
    @30
    @45
    @41
    @35
    wb
    @0
    @40
    @34
    @34
    @40
    @31
    @32
    cR
    vy
    vex
    vx
    vex
    brcnv
    bicomi
    notbii
    a1i
    rabeqbidv
    mpteq12dv
    rneqd
    syl5eq
    #
    fveq2d
    @46
    3eqtr4d
    #
    @27
    syl6eqss
    @29
    syl6ss
    sseld
    @0
    @13
    @16
    vm
    vn
    @6
    @8
    @0
    @10
    @6
    wcel
    #
    @11
    @8
    wcel
    #
    wa
    #
    wa
    #
    @16
    @13
    @12
    @3
    wcel
    @51
    cC
    @3
    @12
    cC
    @1
    ssun2
    @51
    @12
    va
    vb
    cX
    cX
    @31
    va
    cv
    #
    cR
    wbr
    #
    wn
    #
    vb
    cv
    #
    @31
    cR
    wbr
    #
    wn
    #
    wa
    vy
    cX
    crab
    #
    cmpt2
    #
    crn
    #
    cC
    @51
    @12
    @58
    wceq
    #
    vb
    cX
    wrex
    #
    va
    cX
    wrex
    #
    @12
    @60
    wcel
    #
    @0
    @50
    @63
    @0
    @50
    @10
    @54
    vy
    cX
    crab
    #
    wceq
    #
    va
    cX
    wrex
    #
    @11
    @57
    vy
    cX
    crab
    #
    wceq
    #
    vb
    cX
    wrex
    #
    wa
    #
    @63
    @0
    @48
    @67
    @49
    @70
    @0
    @48
    @10
    vx
    cX
    @31
    @32
    cR
    wbr
    #
    wn
    #
    vy
    cX
    crab
    #
    cmpt
    #
    crn
    #
    wcel
    #
    @67
    @0
    @6
    @76
    @10
    @0
    @6
    cA
    @76
    @28
    ordtval.2
    syl6eq
    eleq2d
    @10
    cvv
    wcel
    @77
    @67
    wb
    vm
    vex
    #
    va
    cX
    @65
    @10
    @75
    cvv
    vx
    va
    cX
    @74
    @65
    vx
    va
    weq
    #
    @73
    @54
    vy
    cX
    @79
    @72
    @53
    @32
    @52
    @31
    cR
    breq2
    notbid
    rabbidv
    #
    cbvmptv
    elrnmpt
    ax-mp
    syl6bb
    @0
    @49
    @11
    @44
    wcel
    #
    @70
    @0
    @8
    @44
    @11
    @0
    @8
    cB
    @44
    @47
    ordtval.3
    syl6eq
    eleq2d
    @11
    cvv
    wcel
    @81
    @70
    wb
    vn
    vex
    vb
    cX
    @68
    @11
    @43
    cvv
    vx
    vb
    cX
    @42
    @68
    vx
    vb
    weq
    #
    @41
    @57
    vy
    cX
    @82
    @40
    @56
    @32
    @55
    @31
    cR
    breq1
    notbid
    rabbidv
    #
    cbvmptv
    elrnmpt
    ax-mp
    syl6bb
    anbi12d
    @71
    @66
    @69
    wa
    #
    vb
    cX
    wrex
    #
    va
    cX
    wrex
    @63
    @66
    @69
    va
    vb
    cX
    cX
    reeanv
    @85
    @62
    va
    cX
    @84
    @61
    vb
    cX
    @84
    @12
    @65
    @68
    cin
    #
    @58
    @10
    @65
    @11
    @68
    ineq12
    @54
    @57
    vy
    cX
    inrab
    #
    syl6eq
    reximi
    reximi
    sylbir
    syl6bi
    imp
    @12
    cvv
    wcel
    @64
    @63
    wb
    @10
    @11
    @78
    inex1
    va
    vb
    cX
    cX
    @58
    @12
    @59
    cvv
    @59
    eqid
    #
    elrnmpt2g
    ax-mp
    sylibr
    ordtval.4
    syl6eleqr
    sseldi
    @4
    @12
    @3
    eleq1
    syl5ibrcom
    rexlimdvva
    3jaod
    sylbid
    ssrdv
    @0
    @1
    cC
    @2
    @0
    @19
    @1
    @2
    wss
    #
    @26
    @1
    cvv
    ssfii
    syl
    #
    @0
    cC
    @60
    @2
    ordtval.4
    @0
    cX
    cX
    cxp
    #
    @2
    @59
    wf
    #
    @60
    @2
    wss
    @0
    @58
    @2
    wcel
    #
    vb
    cX
    wral
    va
    cX
    wral
    @92
    @0
    @93
    va
    vb
    cX
    cX
    @0
    @52
    cX
    wcel
    #
    @55
    cX
    wcel
    #
    wa
    #
    wa
    #
    @58
    @86
    @2
    @87
    @97
    @65
    @2
    wcel
    @68
    @2
    wcel
    @86
    @2
    wcel
    @97
    @1
    @2
    @65
    @0
    @89
    @96
    @90
    adantr
    #
    @97
    cA
    @1
    @65
    @20
    @97
    @65
    @76
    cA
    @97
    @65
    @76
    wcel
    #
    @65
    @74
    wceq
    #
    vx
    cX
    wrex
    #
    @97
    @94
    @65
    @65
    wceq
    #
    @101
    @0
    @94
    @95
    simprl
    @97
    @65
    eqidd
    @100
    @102
    vx
    @52
    cX
    @79
    @74
    @65
    @65
    @80
    eqeq2d
    rspcev
    syl2anc
    @97
    cX
    cvv
    wcel
    #
    @65
    cvv
    wcel
    @99
    @101
    wb
    @0
    @103
    @96
    @25
    adantr
    #
    @54
    vy
    cX
    cvv
    rabexg
    vx
    cX
    @74
    @65
    @75
    cvv
    @75
    eqid
    elrnmpt
    3syl
    mpbird
    ordtval.2
    syl6eleqr
    sseldi
    sseldd
    @97
    @1
    @2
    @68
    @98
    @97
    cB
    @1
    @68
    @27
    @97
    @68
    @44
    cB
    @97
    @68
    @44
    wcel
    #
    @68
    @42
    wceq
    #
    vx
    cX
    wrex
    #
    @97
    @95
    @68
    @68
    wceq
    #
    @107
    @0
    @94
    @95
    simprr
    @97
    @68
    eqidd
    @106
    @108
    vx
    @55
    cX
    @82
    @42
    @68
    @68
    @83
    eqeq2d
    rspcev
    syl2anc
    @97
    @103
    @68
    cvv
    wcel
    @105
    @107
    wb
    @104
    @57
    vy
    cX
    cvv
    rabexg
    vx
    cX
    @42
    @68
    @43
    cvv
    @43
    eqid
    elrnmpt
    3syl
    mpbird
    ordtval.3
    syl6eleqr
    sseldi
    sseldd
    @65
    @68
    @1
    fiin
    syl2anc
    syl5eqelr
    ralrimivva
    va
    vb
    cX
    cX
    @58
    @2
    @59
    @88
    fmpt2
    sylib
    @91
    @2
    @59
    frn
    syl
    syl5eqss
    unssd
    eqssd
end
