include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wmo.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "cpr.mm"
include "wcel.mm"
include "brdom5.mm"
include "wceq.mm"
include "cop.mm"
include "cab.mm"
include "wi.mm"
include "wal.mm"
include "zfpair2.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "df-br.mm"
include "anbi2i.mm"
include "syl6bbr.mm"
include "2rexbidv.mm"
include "elab.mm"
include "weq.mm"
include "wne.mm"
include "wb.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "eqtri.mm"
include "disjne.mm"
include "mp3an1.mm"
include "vex.mm"
include "opthpr.mm"
include "syl.mm"
include "breq12.mm"
include "biimprd.mm"
include "syl6bi.mm"
include "impd.mm"
include "ex.mm"
include "adantrd.mm"
include "rexlimdvv.mm"
include "syl5bi.mm"
include "alrimiv.mm"
include "moim.mm"
include "ralimia.mm"
include "ancoms.mm"
include "eqcom.mm"
include "ancom.mm"
include "3bitr4g.mm"
include "bicomi.mm"
include "a1i.mm"
include "anbi12d.mm"
include "rexbidva.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "adantr.mm"
include "breq2.mm"
include "breq1.mm"
include "ceqsrex2v.mm"
include "bitrd.mm"
include "ralbiia.mm"
include "biimpri.mm"
include "csn.mm"
include "snex.mm"
include "simpl.mm"
include "ss2abi.mm"
include "df-sn.mm"
include "sseqtr4i.mm"
include "ssexi.mm"
include "ab2rexex2.mm"
include "eleq2.mm"
include "mobidv.mm"
include "ralbidv.mm"
include "spcev.mm"
include "syl2an.mm"
include "exlimiv.mm"
include "copab.mm"
include "preq1.mm"
include "eleq1d.mm"
include "preq2.mm"
include "eqid.mm"
include "brab.mm"
include "mobii.mm"
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
include "syl2anbr.mm"
include "impbii.mm"
include "bitri.mm"

theorem brdom6disj
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
  assert |- ( A ~<_ B <-> E. f ( A. x e. B E* y { x , y } e. f /\ A. x e. A E. y e. B { y , x } e. f ) )

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
    wmo
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
    wmo
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
    brdom5
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
    wmo
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
    @4
    @32
    vx
    cB
    @0
    cB
    wcel
    #
    @31
    @3
    wi
    #
    vy
    wal
    @4
    @32
    wi
    @37
    @38
    vy
    @31
    @11
    @25
    wceq
    #
    @23
    @24
    @2
    wbr
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
    @37
    @3
    @29
    @42
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
    @41
    vw
    vz
    cA
    cB
    @43
    @28
    @39
    @27
    wa
    @41
    @43
    @26
    @39
    @27
    @22
    @11
    @25
    eqeq1
    anbi1d
    @40
    @27
    @39
    @23
    @24
    @2
    df-br
    #
    anbi2i
    syl6bbr
    2rexbidv
    elab
    @37
    @41
    @3
    vw
    vz
    cA
    cB
    @37
    @24
    cA
    wcel
    #
    @41
    @3
    wi
    #
    @23
    cB
    wcel
    #
    @37
    @45
    @46
    @37
    @45
    wa
    #
    @39
    @40
    @3
    @48
    @39
    vx
    vz
    weq
    vy
    vw
    weq
    wa
    #
    @40
    @3
    wi
    @48
    @0
    @24
    wne
    #
    @39
    @49
    wb
    cB
    cA
    cin
    #
    c0
    wceq
    #
    @37
    @45
    @50
    @51
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
    @49
    @3
    @40
    @0
    @23
    @1
    @24
    @2
    breq12
    biimprd
    syl6bi
    impd
    ex
    adantrd
    rexlimdvv
    syl5bi
    alrimiv
    @31
    @3
    vy
    moim
    syl
    ralimia
    @36
    @8
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
    @58
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
    @40
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
    @58
    @34
    @65
    wb
    @59
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
    @58
    @65
    @29
    @69
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
    @67
    vw
    vz
    cA
    cB
    @70
    @26
    @66
    @27
    @22
    @16
    @25
    eqeq1
    anbi1d
    2rexbidv
    elab
    @58
    @68
    @64
    vw
    cA
    @58
    @67
    @63
    vz
    cB
    @58
    @47
    wa
    #
    @66
    @62
    @27
    @40
    @71
    @25
    @16
    wceq
    #
    @61
    @60
    wa
    #
    @66
    @62
    @71
    @23
    @0
    wne
    #
    @72
    @73
    wb
    @47
    @58
    @74
    @52
    @47
    @58
    @74
    @53
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
    @56
    @57
    @55
    @54
    opthpr
    syl
    @16
    @25
    eqcom
    @60
    @61
    ancom
    3bitr4g
    @27
    @40
    wb
    @71
    @40
    @27
    @44
    bicomi
    a1i
    anbi12d
    rexbidva
    rexbidv
    syl5bb
    adantr
    @40
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
    biimpri
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
    @75
    @26
    vv
    cab
    @76
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
    @77
    @14
    @32
    vx
    cB
    @77
    @13
    @31
    vy
    @12
    @30
    @11
    eleq2
    mobidv
    ralbidv
    @77
    @18
    @35
    vx
    cA
    @77
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
    syl2an
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
    wmo
    #
    vx
    cB
    wral
    #
    @1
    @0
    @80
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
    @82
    @14
    vx
    cB
    @81
    @13
    vy
    @79
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
    @80
    @54
    @55
    @60
    @78
    @87
    @12
    @24
    @0
    @23
    preq1
    eleq1d
    @61
    @87
    @11
    @12
    @23
    @1
    @0
    preq2
    eleq1d
    @80
    eqid
    #
    brab
    mobii
    ralbii
    @85
    @18
    vx
    cA
    @84
    @17
    vy
    cB
    @79
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
    @80
    @55
    @54
    vw
    vy
    weq
    @78
    @89
    @12
    @24
    @1
    @23
    preq1
    eleq1d
    vz
    vx
    weq
    @89
    @16
    @12
    @23
    @0
    @1
    preq2
    eleq1d
    @88
    brab
    rexbii
    ralbii
    @9
    @83
    @86
    wa
    vg
    @80
    @80
    @22
    @24
    @23
    cop
    #
    wceq
    #
    @79
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
    @79
    vw
    vz
    vv
    df-opab
    @93
    vw
    vv
    @12
    cuni
    #
    vf
    vuniex
    #
    @92
    @24
    @94
    wcel
    #
    vz
    @79
    @96
    @91
    @24
    @78
    wcel
    @79
    @96
    @24
    @23
    @57
    prid1
    @24
    @78
    @12
    elunii
    mpan
    adantl
    exlimiv
    @92
    vz
    vv
    @94
    @95
    @79
    @23
    @94
    wcel
    #
    @91
    @23
    @78
    wcel
    @79
    @97
    @24
    @23
    @56
    prid2
    @23
    @78
    @12
    elunii
    mpan
    adantl
    @92
    vv
    cab
    @91
    vv
    cab
    #
    @90
    csn
    @98
    cvv
    vv
    @90
    df-sn
    @90
    snex
    eqeltrri
    @92
    @91
    vv
    @91
    @79
    simpl
    ss2abi
    ssexi
    abexex
    abexex
    eqeltri
    @2
    @80
    wceq
    #
    @5
    @83
    @8
    @86
    @99
    @4
    @82
    vx
    cB
    @99
    @3
    @81
    vy
    @0
    @1
    @2
    @80
    breq
    mobidv
    ralbidv
    @99
    @7
    @85
    vx
    cA
    @99
    @6
    @84
    vy
    cB
    @1
    @0
    @2
    @80
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
