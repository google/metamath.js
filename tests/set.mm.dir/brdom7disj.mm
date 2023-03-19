include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wrmo.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "cpr.mm"
include "wcel.mm"
include "brdom4.mm"
include "wceq.mm"
include "cop.mm"
include "cab.mm"
include "weq.mm"
include "wb.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "eqtri.mm"
include "disjne.mm"
include "mp3an1.mm"
include "vex.mm"
include "opthpr.mm"
include "syl.mm"
include "equcom.mm"
include "anbi12i.mm"
include "syl6rbb.mm"
include "df-br.mm"
include "a1i.mm"
include "anbi12d.mm"
include "rexbidva.mm"
include "rexbidv.mm"
include "rexcom.mm"
include "zfpair2.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "elab.mm"
include "bitr4i.mm"
include "adantr.mm"
include "breq1.mm"
include "breq2.mm"
include "ceqsrex2v.mm"
include "bitrd.mm"
include "rmobidva.mm"
include "ralbiia.mm"
include "ancoms.mm"
include "eqcom.mm"
include "ancom.mm"
include "3bitr4g.mm"
include "bicomi.mm"
include "syl5bb.mm"
include "csn.mm"
include "snex.mm"
include "simpl.mm"
include "ss2abi.mm"
include "df-sn.mm"
include "sseqtr4i.mm"
include "ssexi.mm"
include "ab2rexex2.mm"
include "eleq2.mm"
include "rmobidv.mm"
include "ralbidv.mm"
include "spcev.mm"
include "syl2anbr.mm"
include "exlimiv.mm"
include "copab.mm"
include "preq1.mm"
include "eleq1d.mm"
include "preq2.mm"
include "eqid.mm"
include "brab.mm"
include "rmobii.mm"
include "ralbii.mm"
include "rexbii.mm"
include "cvv.mm"
include "df-opab.mm"
include "cuni.mm"
include "vuniex.mm"
include "prid1.mm"
include "elunii.mm"
include "mpan.mm"
include "adantl.mm"
include "prid2.mm"
include "eqeltrri.mm"
include "abexex.mm"
include "eqeltri.mm"
include "breq.mm"
include "impbii.mm"
include "bitri.mm"

theorem brdom7disj
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume brdom7disj.1: |- A e. _V
  assume brdom7disj.2: |- B e. _V
  assume brdom7disj.3: |- ( A i^i B ) = (/)

  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint f g
  disjoint f v
  disjoint f w
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint g v
  disjoint g w
  disjoint g z
  disjoint v x
  disjoint w x
  disjoint x z
  disjoint v y
  disjoint w y
  disjoint y z
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint v w
  disjoint v z
  disjoint w z
  disjoint B g
  disjoint B v
  disjoint B w
  disjoint B z
  assert |- ( A ~<_ B <-> E. f ( A. x e. B E* y e. A { x , y } e. f /\ A. x e. A E. y e. B { y , x } e. f ) )

  proof
    cA
    cB
    cdom
    wbr
    vx
    cv
    #
    vy
    cv
    #
    vg
    cv
    #
    wbr
    #
    vy
    cA
    wrmo
    #
    vx
    cB
    wral
    #
    @1
    @0
    @2
    wbr
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    wa
    #
    vg
    wex
    #
    @0
    @1
    cpr
    #
    vf
    cv
    #
    wcel
    #
    vy
    cA
    wrmo
    #
    vx
    cB
    wral
    #
    @1
    @0
    cpr
    #
    @12
    wcel
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    vx
    vy
    cA
    cB
    vg
    brdom7disj.2
    brdom4
    @10
    @21
    @9
    @21
    vg
    @5
    @11
    vv
    cv
    #
    vz
    cv
    #
    vw
    cv
    #
    cpr
    #
    wceq
    #
    @23
    @24
    cop
    @2
    wcel
    #
    wa
    #
    vz
    cB
    wrex
    vw
    cA
    wrex
    #
    vv
    cab
    #
    wcel
    #
    vy
    cA
    wrmo
    #
    vx
    cB
    wral
    #
    @16
    @30
    wcel
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    @21
    @8
    @32
    @4
    vx
    cB
    @0
    cB
    wcel
    #
    @31
    @3
    vy
    cA
    @37
    @1
    cA
    wcel
    #
    wa
    @31
    vz
    vx
    weq
    #
    vw
    vy
    weq
    #
    wa
    #
    @23
    @24
    @2
    wbr
    #
    wa
    #
    vw
    cA
    wrex
    #
    vz
    cB
    wrex
    #
    @3
    @37
    @31
    @45
    wb
    @38
    @37
    @45
    @11
    @25
    wceq
    #
    @27
    wa
    #
    vw
    cA
    wrex
    #
    vz
    cB
    wrex
    #
    @31
    @37
    @44
    @48
    vz
    cB
    @37
    @43
    @47
    vw
    cA
    @37
    @24
    cA
    wcel
    #
    wa
    #
    @41
    @46
    @42
    @27
    @51
    @46
    vx
    vz
    weq
    #
    vy
    vw
    weq
    #
    wa
    #
    @41
    @51
    @0
    @24
    wne
    #
    @46
    @54
    wb
    cB
    cA
    cin
    #
    c0
    wceq
    #
    @37
    @50
    @55
    @56
    cA
    cB
    cin
    c0
    cB
    cA
    incom
    brdom7disj.3
    eqtri
    #
    cB
    cA
    @0
    @24
    disjne
    mp3an1
    @0
    @1
    @23
    @24
    vx
    vex
    #
    vy
    vex
    #
    vz
    vex
    #
    vw
    vex
    #
    opthpr
    syl
    @52
    @39
    @53
    @40
    vx
    vz
    equcom
    vy
    vw
    equcom
    anbi12i
    syl6rbb
    @42
    @27
    wb
    @51
    @23
    @24
    @2
    df-br
    #
    a1i
    anbi12d
    rexbidva
    rexbidv
    @49
    @47
    vz
    cB
    wrex
    vw
    cA
    wrex
    #
    @31
    @47
    vz
    vw
    cB
    cA
    rexcom
    @29
    @64
    vv
    @11
    vx
    vy
    zfpair2
    @22
    @11
    wceq
    #
    @28
    @47
    vw
    vz
    cA
    cB
    @65
    @26
    @46
    @27
    @22
    @11
    @25
    eqeq1
    anbi1d
    2rexbidv
    elab
    bitr4i
    syl6rbb
    adantr
    @42
    @0
    @24
    @2
    wbr
    @3
    vz
    vw
    @0
    @1
    cB
    cA
    @23
    @0
    @24
    @2
    breq1
    @24
    @1
    @0
    @2
    breq2
    ceqsrex2v
    bitrd
    rmobidva
    ralbiia
    @35
    @7
    vx
    cA
    @0
    cA
    wcel
    #
    @34
    @6
    vy
    cB
    @66
    @1
    cB
    wcel
    #
    wa
    @34
    vw
    vx
    weq
    #
    vz
    vy
    weq
    #
    wa
    #
    @42
    wa
    #
    vz
    cB
    wrex
    #
    vw
    cA
    wrex
    #
    @6
    @66
    @34
    @73
    wb
    @67
    @34
    @16
    @25
    wceq
    #
    @27
    wa
    #
    vz
    cB
    wrex
    #
    vw
    cA
    wrex
    #
    @66
    @73
    @29
    @77
    vv
    @16
    vy
    vx
    zfpair2
    @22
    @16
    wceq
    #
    @28
    @75
    vw
    vz
    cA
    cB
    @78
    @26
    @74
    @27
    @22
    @16
    @25
    eqeq1
    anbi1d
    2rexbidv
    elab
    @66
    @76
    @72
    vw
    cA
    @66
    @75
    @71
    vz
    cB
    @66
    @23
    cB
    wcel
    #
    wa
    #
    @74
    @70
    @27
    @42
    @80
    @25
    @16
    wceq
    #
    @69
    @68
    wa
    #
    @74
    @70
    @80
    @23
    @0
    wne
    #
    @81
    @82
    wb
    @79
    @66
    @83
    @57
    @79
    @66
    @83
    @58
    cB
    cA
    @23
    @0
    disjne
    mp3an1
    ancoms
    @23
    @24
    @1
    @0
    @61
    @62
    @60
    @59
    opthpr
    syl
    @16
    @25
    eqcom
    @68
    @69
    ancom
    3bitr4g
    @27
    @42
    wb
    @80
    @42
    @27
    @63
    bicomi
    a1i
    anbi12d
    rexbidva
    rexbidv
    syl5bb
    adantr
    @42
    @23
    @0
    @2
    wbr
    @6
    vw
    vz
    @0
    @1
    cA
    cB
    @24
    @0
    @23
    @2
    breq2
    @23
    @1
    @0
    @2
    breq1
    ceqsrex2v
    bitrd
    rexbidva
    ralbiia
    @20
    @33
    @36
    wa
    vf
    @30
    @28
    vw
    vz
    vv
    cA
    cB
    brdom7disj.1
    brdom7disj.2
    @28
    vv
    cab
    #
    @25
    csn
    #
    @25
    snex
    @84
    @26
    vv
    cab
    @85
    @28
    @26
    vv
    @26
    @27
    simpl
    ss2abi
    vv
    @25
    df-sn
    sseqtr4i
    ssexi
    ab2rexex2
    @12
    @30
    wceq
    #
    @15
    @33
    @19
    @36
    @86
    @14
    @32
    vx
    cB
    @86
    @13
    @31
    vy
    cA
    @12
    @30
    @11
    eleq2
    rmobidv
    ralbidv
    @86
    @18
    @35
    vx
    cA
    @86
    @17
    @34
    vy
    cB
    @12
    @30
    @16
    eleq2
    rexbidv
    ralbidv
    anbi12d
    spcev
    syl2anbr
    exlimiv
    @20
    @10
    vf
    @15
    @0
    @1
    @24
    @23
    cpr
    #
    @12
    wcel
    #
    vw
    vz
    copab
    #
    wbr
    #
    vy
    cA
    wrmo
    #
    vx
    cB
    wral
    #
    @1
    @0
    @89
    wbr
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    @10
    @19
    @91
    @14
    vx
    cB
    @90
    @13
    vy
    cA
    @88
    @0
    @23
    cpr
    #
    @12
    wcel
    @13
    vw
    vz
    @0
    @1
    @89
    @59
    @60
    @68
    @87
    @96
    @12
    @24
    @0
    @23
    preq1
    eleq1d
    @69
    @96
    @11
    @12
    @23
    @1
    @0
    preq2
    eleq1d
    @89
    eqid
    #
    brab
    rmobii
    ralbii
    @94
    @18
    vx
    cA
    @93
    @17
    vy
    cB
    @88
    @1
    @23
    cpr
    #
    @12
    wcel
    @17
    vw
    vz
    @1
    @0
    @89
    @60
    @59
    @40
    @87
    @98
    @12
    @24
    @1
    @23
    preq1
    eleq1d
    @39
    @98
    @16
    @12
    @23
    @0
    @1
    preq2
    eleq1d
    @97
    brab
    rexbii
    ralbii
    @9
    @92
    @95
    wa
    vg
    @89
    @89
    @22
    @24
    @23
    cop
    #
    wceq
    #
    @88
    wa
    #
    vz
    wex
    #
    vw
    wex
    vv
    cab
    cvv
    @88
    vw
    vz
    vv
    df-opab
    @102
    vw
    vv
    @12
    cuni
    #
    vf
    vuniex
    #
    @101
    @24
    @103
    wcel
    #
    vz
    @88
    @105
    @100
    @24
    @87
    wcel
    @88
    @105
    @24
    @23
    @62
    prid1
    @24
    @87
    @12
    elunii
    mpan
    adantl
    exlimiv
    @101
    vz
    vv
    @103
    @104
    @88
    @23
    @103
    wcel
    #
    @100
    @23
    @87
    wcel
    @88
    @106
    @24
    @23
    @61
    prid2
    @23
    @87
    @12
    elunii
    mpan
    adantl
    @101
    vv
    cab
    @100
    vv
    cab
    #
    @99
    csn
    @107
    cvv
    vv
    @99
    df-sn
    @99
    snex
    eqeltrri
    @101
    @100
    vv
    @100
    @88
    simpl
    ss2abi
    ssexi
    abexex
    abexex
    eqeltri
    @2
    @89
    wceq
    #
    @5
    @92
    @8
    @95
    @108
    @4
    @91
    vx
    cB
    @108
    @3
    @90
    vy
    cA
    @0
    @1
    @2
    @89
    breq
    rmobidv
    ralbidv
    @108
    @7
    @94
    vx
    cA
    @108
    @6
    @93
    vy
    cB
    @1
    @0
    @2
    @89
    breq
    rexbidv
    ralbidv
    anbi12d
    spcev
    syl2anbr
    exlimiv
    impbii
    bitri
end
