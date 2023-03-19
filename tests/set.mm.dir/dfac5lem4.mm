include "cv.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "wcel.mm"
include "weu.mm"
include "wex.mm"
include "csn.mm"
include "cxp.mm"
include "wrex.mm"
include "wa.mm"
include "cab.mm"
include "vex.mm"
include "weq.mm"
include "neeq1.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "elab.mm"
include "simplbi.mm"
include "eleq2s.mm"
include "rgen.mm"
include "wel.mm"
include "wn.mm"
include "wal.mm"
include "df-an.mm"
include "elab2.mm"
include "simprbi.mm"
include "sneq.mm"
include "xpeq1d.mm"
include "xpeq2.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "cop.mm"
include "eleq2.mm"
include "elxp.mm"
include "excom.mm"
include "bitri.mm"
include "syl6bb.mm"
include "bi2anan9.mm"
include "eeanv.mm"
include "syl6bbr.mm"
include "velsn.mm"
include "opeq1.mm"
include "biimpac.mm"
include "sylan2b.mm"
include "adantrr.mm"
include "exlimiv.mm"
include "sylan9req.mm"
include "opth1.mm"
include "syl.mm"
include "exlimivv.mm"
include "syl6bi.mm"
include "syl6.mm"
include "eqeq12.mm"
include "sylibrd.mm"
include "ex.mm"
include "rexlimivw.mm"
include "rexlimdvw.mm"
include "imp.mm"
include "syl2an.mm"
include "syl5bir.mm"
include "necon1ad.mm"
include "alrimdv.mm"
include "disj1.mm"
include "syl6ibr.mm"
include "rgen2a.mm"
include "cvv.mm"
include "cuni.mm"
include "cpw.mm"
include "vuniex.mm"
include "xpex.mm"
include "pwex.mm"
include "wss.mm"
include "snssi.mm"
include "elssuni.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "snex.mm"
include "elpw.mm"
include "sylibr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "adantl.mm"
include "abssi.mm"
include "ssexi.mm"
include "eqeltri.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "spcv.mm"
include "sylbi.mm"
include "mp2ani.mm"

theorem dfac5lem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let vh: setvar h
  let vf: setvar f
  let vg: setvar g
  assume dfac5lem.1: |- A = { u | ( u =/= (/) /\ E. t e. h u = ( { t } X. t ) ) }
  assume dfac5lem.2: |- B = ( U. A i^i y )
  assume dfac5lem.3: |- ( ph <-> A. x ( ( A. z e. x z =/= (/) /\ A. z e. x A. w e. x ( z =/= w -> ( z i^i w ) = (/) ) ) -> E. y A. z e. x E! v v e. ( z i^i y ) ) )

  disjoint x z
  disjoint x y
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint h x
  disjoint y z
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint h z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint h y
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint h w
  disjoint u v
  disjoint t v
  disjoint h v
  disjoint t u
  disjoint h u
  disjoint h t
  disjoint B z
  disjoint B w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint f x
  disjoint f z
  disjoint f y
  disjoint f w
  disjoint f v
  disjoint f u
  disjoint f t
  disjoint f h
  disjoint f g
  disjoint g x
  disjoint g z
  disjoint g y
  disjoint g w
  disjoint g v
  disjoint g u
  disjoint g t
  disjoint g h
  disjoint B f
  disjoint B g
  disjoint A g
  assert |- ( ph -> E. y A. z e. A E! v v e. ( z i^i y ) )

  proof
    wph
    vz
    cv
    #
    c0
    wne
    #
    vz
    cA
    wral
    #
    @0
    vw
    cv
    #
    wne
    #
    @0
    @3
    cin
    c0
    wceq
    #
    wi
    #
    vw
    cA
    wral
    #
    vz
    cA
    wral
    #
    vv
    cv
    #
    @0
    vy
    cv
    #
    cin
    wcel
    vv
    weu
    #
    vz
    cA
    wral
    #
    vy
    wex
    #
    @1
    vz
    cA
    @1
    @0
    vu
    cv
    #
    c0
    wne
    #
    @14
    vt
    cv
    #
    csn
    #
    @16
    cxp
    #
    wceq
    #
    vt
    vh
    cv
    #
    wrex
    #
    wa
    #
    vu
    cab
    #
    cA
    @0
    @23
    wcel
    @1
    @0
    @18
    wceq
    #
    vt
    @20
    wrex
    #
    @22
    @1
    @25
    wa
    #
    vu
    @0
    vz
    vex
    #
    vu
    vz
    weq
    #
    @15
    @1
    @21
    @25
    @14
    @0
    c0
    neeq1
    @28
    @19
    @24
    vt
    @20
    @14
    @0
    @18
    eqeq1
    rexbidv
    anbi12d
    #
    elab
    simplbi
    dfac5lem.1
    eleq2s
    rgen
    @6
    vz
    vw
    cA
    @0
    cA
    wcel
    #
    @3
    cA
    wcel
    #
    wa
    #
    @4
    vx
    vz
    wel
    #
    vx
    vw
    wel
    #
    wn
    wi
    #
    vx
    wal
    @5
    @32
    @4
    @35
    vx
    @32
    @35
    @0
    @3
    @35
    wn
    @33
    @34
    wa
    #
    @32
    vz
    vw
    weq
    #
    @33
    @34
    df-an
    @30
    @25
    @3
    vg
    cv
    #
    csn
    #
    @38
    cxp
    #
    wceq
    #
    vg
    @20
    wrex
    #
    @36
    @37
    wi
    #
    @31
    @30
    @1
    @25
    @22
    @26
    vu
    @0
    cA
    @27
    @29
    dfac5lem.1
    elab2
    simprbi
    @31
    @3
    @18
    wceq
    #
    vt
    @20
    wrex
    #
    @42
    @31
    @3
    c0
    wne
    #
    @45
    @22
    @46
    @45
    wa
    vu
    @3
    cA
    vw
    vex
    vu
    vw
    weq
    #
    @15
    @46
    @21
    @45
    @14
    @3
    c0
    neeq1
    @47
    @19
    @44
    vt
    @20
    @14
    @3
    @18
    eqeq1
    rexbidv
    anbi12d
    dfac5lem.1
    elab2
    simprbi
    @44
    @41
    vt
    vg
    @20
    vt
    vg
    weq
    #
    @18
    @40
    @3
    @48
    @18
    @39
    @16
    cxp
    @40
    @48
    @17
    @39
    @16
    @16
    @38
    sneq
    xpeq1d
    @16
    @38
    @39
    xpeq2
    eqtrd
    #
    eqeq2d
    cbvrexv
    sylib
    @25
    @42
    @43
    @25
    @41
    @43
    vg
    @20
    @24
    @41
    @43
    wi
    vt
    @20
    @24
    @41
    @43
    @24
    @41
    wa
    #
    @36
    @18
    @40
    wceq
    #
    @37
    @50
    @36
    @48
    @51
    @50
    @36
    vx
    cv
    #
    @14
    @9
    cop
    #
    wceq
    #
    @14
    @17
    wcel
    #
    vv
    vt
    wel
    #
    wa
    wa
    #
    vu
    wex
    #
    @52
    @14
    @10
    cop
    #
    wceq
    #
    @14
    @39
    wcel
    #
    vy
    vg
    wel
    #
    wa
    wa
    #
    vu
    wex
    #
    wa
    #
    vy
    wex
    vv
    wex
    #
    @48
    @50
    @36
    @58
    vv
    wex
    #
    @64
    vy
    wex
    #
    wa
    @66
    @24
    @33
    @67
    @41
    @34
    @68
    @24
    @33
    @52
    @18
    wcel
    #
    @67
    @0
    @18
    @52
    eleq2
    @69
    @57
    vv
    wex
    vu
    wex
    @67
    vu
    vv
    @52
    @17
    @16
    elxp
    @57
    vu
    vv
    excom
    bitri
    syl6bb
    @41
    @34
    @52
    @40
    wcel
    #
    @68
    @3
    @40
    @52
    eleq2
    @70
    @63
    vy
    wex
    vu
    wex
    @68
    vu
    vy
    @52
    @39
    @38
    elxp
    @63
    vu
    vy
    excom
    bitri
    syl6bb
    bi2anan9
    @58
    @64
    vv
    vy
    eeanv
    syl6bbr
    @65
    @48
    vv
    vy
    @65
    @16
    @9
    cop
    #
    @38
    @10
    cop
    #
    wceq
    @48
    @58
    @64
    @71
    @52
    @72
    @57
    @52
    @71
    wceq
    #
    vu
    @54
    @55
    @73
    @56
    @55
    @54
    vu
    vt
    weq
    #
    @73
    vu
    @16
    velsn
    @74
    @54
    @73
    @74
    @53
    @71
    @52
    @14
    @16
    @9
    opeq1
    eqeq2d
    biimpac
    sylan2b
    adantrr
    exlimiv
    @63
    @52
    @72
    wceq
    #
    vu
    @60
    @61
    @75
    @62
    @61
    @60
    vu
    vg
    weq
    #
    @75
    vu
    @38
    velsn
    @76
    @60
    @75
    @76
    @59
    @72
    @52
    @14
    @38
    @10
    opeq1
    eqeq2d
    biimpac
    sylan2b
    adantrr
    exlimiv
    sylan9req
    @16
    @9
    @38
    @10
    vt
    vex
    #
    vv
    vex
    opth1
    syl
    exlimivv
    syl6bi
    @49
    syl6
    @0
    @18
    @3
    @40
    eqeq12
    sylibrd
    ex
    rexlimivw
    rexlimdvw
    imp
    syl2an
    syl5bir
    necon1ad
    alrimdv
    vx
    @0
    @3
    disj1
    syl6ibr
    rgen2a
    wph
    @1
    vz
    @52
    wral
    #
    @6
    vw
    @52
    wral
    #
    vz
    @52
    wral
    #
    wa
    #
    @11
    vz
    @52
    wral
    #
    vy
    wex
    #
    wi
    #
    vx
    wal
    @2
    @8
    wa
    #
    @13
    wi
    #
    dfac5lem.3
    @84
    @86
    vx
    cA
    cA
    @23
    cvv
    dfac5lem.1
    @23
    @20
    @20
    cuni
    #
    cxp
    #
    cpw
    #
    @88
    @20
    @87
    vh
    vex
    vh
    vuniex
    xpex
    pwex
    @22
    vu
    @89
    @21
    @14
    @89
    wcel
    #
    @15
    @19
    @90
    vt
    @20
    vt
    vh
    wel
    #
    @90
    @19
    @18
    @89
    wcel
    #
    @91
    @18
    @88
    wss
    #
    @92
    @91
    @17
    @20
    wss
    @16
    @87
    wss
    @93
    @16
    @20
    snssi
    @16
    @20
    elssuni
    @17
    @20
    @16
    @87
    xpss12
    syl2anc
    @18
    @88
    @17
    @16
    @16
    snex
    @77
    xpex
    elpw
    sylibr
    @14
    @18
    @89
    eleq1
    syl5ibrcom
    rexlimiv
    adantl
    abssi
    ssexi
    eqeltri
    @52
    cA
    wceq
    #
    @81
    @85
    @83
    @13
    @94
    @78
    @2
    @80
    @8
    @1
    vz
    @52
    cA
    raleq
    @79
    @7
    vz
    @52
    cA
    @6
    vw
    @52
    cA
    raleq
    raleqbi1dv
    anbi12d
    @94
    @82
    @12
    vy
    @11
    vz
    @52
    cA
    raleq
    exbidv
    imbi12d
    spcv
    sylbi
    mp2ani
end
