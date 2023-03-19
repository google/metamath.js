include "ctb.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "cxp.mm"
include "wceq.mm"
include "cmpt2.mm"
include "crn.mm"
include "cab.mm"
include "xpeq1.mm"
include "xpeq2.mm"
include "cbvmpt2v.mm"
include "rnmpt2.mm"
include "eqtri.mm"
include "abeq2i.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "cop.mm"
include "basis2.mm"
include "exp43.mm"
include "imp42.mm"
include "opelxpi.mm"
include "xpss12.mm"
include "anim12i.mm"
include "an4s.mm"
include "reximi.mm"
include "sylbir.mm"
include "syl2an.mm"
include "ralrimivva.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "ralxp.mm"
include "sylibr.mm"
include "anassrs.mm"
include "ineq12.mm"
include "inxp.mm"
include "syl6eq.mm"
include "sseq2d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "rexeqi.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "xpex.mm"
include "rgenw.mm"
include "cmpt.mm"
include "vex.mm"
include "op1std.mm"
include "op2ndd.mm"
include "xpeq12d.mm"
include "mpt2mpt.mm"
include "eqcomi.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rexrnmpt.mm"
include "ax-mp.mm"
include "eleq2d.mm"
include "sseq1d.mm"
include "rexxp.mm"
include "3bitri.mm"
include "syl6bb.mm"
include "raleqbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "syl5bi.mm"
include "ralrimivv.mm"
include "txbasex.mm"
include "isbasis2g.mm"
include "syl.mm"
include "mpbird.mm"

theorem txbas
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let vw: setvar w
  let cX: class X
  let cY: class Y
  assume txval.1: |- B = ran ( x e. R , y e. S |-> ( x X. y ) )

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a p
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint R a
  disjoint b c
  disjoint b d
  disjoint b p
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint R b
  disjoint c d
  disjoint c p
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint R c
  disjoint d p
  disjoint d r
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint R d
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint R p
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint R r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint R s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint R t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint R u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint R v
  disjoint x z
  disjoint y z
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S p
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S z
  disjoint a w
  disjoint B a
  disjoint b w
  disjoint B b
  disjoint c w
  disjoint B c
  disjoint d w
  disjoint B d
  disjoint p w
  disjoint B p
  disjoint r w
  disjoint B r
  disjoint s w
  disjoint B s
  disjoint t w
  disjoint B t
  disjoint u w
  disjoint B u
  disjoint v w
  disjoint B v
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  assert |- ( ( R e. TopBases /\ S e. TopBases ) -> B e. TopBases )

  proof
    cR
    ctb
    wcel
    #
    cS
    ctb
    wcel
    #
    wa
    #
    cB
    ctb
    wcel
    #
    vp
    cv
    #
    vt
    cv
    #
    wcel
    #
    @5
    vu
    cv
    #
    vv
    cv
    #
    cin
    #
    wss
    #
    wa
    #
    vt
    cB
    wrex
    #
    vp
    @9
    wral
    #
    vv
    cB
    wral
    vu
    cB
    wral
    #
    @2
    @13
    vu
    vv
    cB
    cB
    @7
    cB
    wcel
    #
    @8
    cB
    wcel
    #
    wa
    #
    @7
    va
    cv
    #
    vb
    cv
    #
    cxp
    #
    wceq
    #
    vb
    cS
    wrex
    #
    @8
    vc
    cv
    #
    vd
    cv
    #
    cxp
    #
    wceq
    #
    vd
    cS
    wrex
    #
    wa
    #
    vc
    cR
    wrex
    va
    cR
    wrex
    #
    @2
    @13
    @17
    @22
    va
    cR
    wrex
    #
    @27
    vc
    cR
    wrex
    #
    wa
    @29
    @15
    @30
    @16
    @31
    @30
    vu
    cB
    cB
    vx
    vy
    cR
    cS
    vx
    cv
    #
    vy
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    @30
    vu
    cab
    txval.1
    va
    vb
    vu
    cR
    cS
    @20
    @35
    vx
    vy
    va
    vb
    cR
    cS
    @34
    @20
    @18
    @33
    cxp
    @32
    @18
    @33
    xpeq1
    @33
    @19
    @18
    xpeq2
    cbvmpt2v
    rnmpt2
    eqtri
    abeq2i
    @31
    vv
    cB
    cB
    @36
    @31
    vv
    cab
    txval.1
    vc
    vd
    vv
    cR
    cS
    @25
    @35
    vx
    vy
    vc
    vd
    cR
    cS
    @34
    @25
    @23
    @33
    cxp
    @32
    @23
    @33
    xpeq1
    @33
    @24
    @23
    xpeq2
    cbvmpt2v
    rnmpt2
    eqtri
    abeq2i
    anbi12i
    @22
    @27
    va
    vc
    cR
    cR
    reeanv
    bitr4i
    @2
    @28
    @13
    va
    vc
    cR
    cR
    @28
    @21
    @26
    wa
    #
    vd
    cS
    wrex
    vb
    cS
    wrex
    @2
    @18
    cR
    wcel
    #
    @23
    cR
    wcel
    #
    wa
    #
    wa
    #
    @13
    @21
    @26
    vb
    vd
    cS
    cS
    reeanv
    @41
    @37
    @13
    vb
    vd
    cS
    cS
    @41
    @19
    cS
    wcel
    #
    @24
    cS
    wcel
    #
    wa
    #
    wa
    @13
    @37
    @4
    @34
    wcel
    #
    @34
    @18
    @23
    cin
    #
    @19
    @24
    cin
    #
    cxp
    #
    wss
    #
    wa
    #
    vy
    cS
    wrex
    vx
    cR
    wrex
    #
    vp
    @48
    wral
    #
    @2
    @40
    @44
    @52
    @0
    @40
    @1
    @44
    @52
    @0
    @40
    wa
    #
    @1
    @44
    wa
    #
    wa
    #
    @7
    @8
    cop
    #
    @34
    wcel
    #
    @49
    wa
    #
    vy
    cS
    wrex
    #
    vx
    cR
    wrex
    #
    vv
    @47
    wral
    vu
    @46
    wral
    @52
    @55
    @60
    vu
    vv
    @46
    @47
    @53
    @7
    @46
    wcel
    #
    @54
    @8
    @47
    wcel
    #
    @60
    @53
    @61
    wa
    @7
    @32
    wcel
    #
    @32
    @46
    wss
    #
    wa
    #
    vx
    cR
    wrex
    #
    @8
    @33
    wcel
    #
    @33
    @47
    wss
    #
    wa
    #
    vy
    cS
    wrex
    #
    @60
    @54
    @62
    wa
    @0
    @38
    @39
    @61
    @66
    @0
    @38
    @39
    @61
    @66
    vx
    @7
    cR
    @18
    @23
    basis2
    exp43
    imp42
    @1
    @42
    @43
    @62
    @70
    @1
    @42
    @43
    @62
    @70
    vy
    @8
    cS
    @19
    @24
    basis2
    exp43
    imp42
    @66
    @70
    wa
    @65
    @69
    wa
    #
    vy
    cS
    wrex
    #
    vx
    cR
    wrex
    @60
    @65
    @69
    vx
    vy
    cR
    cS
    reeanv
    @72
    @59
    vx
    cR
    @71
    @58
    vy
    cS
    @63
    @67
    @64
    @68
    @58
    @63
    @67
    wa
    @57
    @64
    @68
    wa
    @49
    @7
    @8
    @32
    @33
    opelxpi
    @32
    @46
    @33
    @47
    xpss12
    anim12i
    an4s
    reximi
    reximi
    sylbir
    syl2an
    an4s
    ralrimivva
    @51
    @60
    vp
    vu
    vv
    @46
    @47
    @4
    @56
    wceq
    #
    @50
    @58
    vx
    vy
    cR
    cS
    @73
    @45
    @57
    @49
    @4
    @56
    @34
    eleq1
    anbi1d
    2rexbidv
    ralxp
    sylibr
    an4s
    anassrs
    @37
    @12
    @51
    vp
    @9
    @48
    @37
    @9
    @20
    @25
    cin
    @48
    @7
    @20
    @8
    @25
    ineq12
    @18
    @19
    @23
    @24
    inxp
    syl6eq
    #
    @37
    @12
    @6
    @5
    @48
    wss
    #
    wa
    #
    vt
    cB
    wrex
    #
    @51
    @37
    @11
    @76
    vt
    cB
    @37
    @10
    @75
    @6
    @37
    @9
    @48
    @5
    @74
    sseq2d
    anbi2d
    rexbidv
    @77
    @76
    vt
    @36
    wrex
    #
    @4
    vz
    cv
    #
    c1st
    cfv
    #
    @79
    c2nd
    cfv
    #
    cxp
    #
    wcel
    #
    @82
    @48
    wss
    #
    wa
    #
    vz
    cR
    cS
    cxp
    #
    wrex
    #
    @51
    @76
    vt
    cB
    @36
    txval.1
    rexeqi
    @82
    cvv
    wcel
    #
    vz
    @86
    wral
    @78
    @87
    wb
    @88
    vz
    @86
    @80
    @81
    @79
    c1st
    fvex
    @79
    c2nd
    fvex
    xpex
    rgenw
    @76
    @85
    vz
    vt
    @86
    @82
    @35
    cvv
    vz
    @86
    @82
    cmpt
    @35
    vx
    vy
    vz
    cR
    cS
    @82
    @34
    @79
    @32
    @33
    cop
    wceq
    #
    @80
    @32
    @81
    @33
    @32
    @33
    @79
    vx
    vex
    #
    vy
    vex
    #
    op1std
    @32
    @33
    @79
    @90
    @91
    op2ndd
    xpeq12d
    #
    mpt2mpt
    eqcomi
    @5
    @82
    wceq
    @6
    @83
    @75
    @84
    @5
    @82
    @4
    eleq2
    @5
    @82
    @48
    sseq1
    anbi12d
    rexrnmpt
    ax-mp
    @85
    @50
    vz
    vx
    vy
    cR
    cS
    @89
    @83
    @45
    @84
    @49
    @89
    @82
    @34
    @4
    @92
    eleq2d
    @89
    @82
    @34
    @48
    @92
    sseq1d
    anbi12d
    rexxp
    3bitri
    syl6bb
    raleqbidv
    syl5ibrcom
    rexlimdvva
    syl5bir
    rexlimdvva
    syl5bi
    ralrimivv
    @2
    cB
    cvv
    wcel
    @3
    @14
    wb
    vx
    vy
    cB
    cR
    cS
    ctb
    ctb
    txval.1
    txbasex
    vu
    vv
    vp
    vt
    cB
    cvv
    isbasis2g
    syl
    mpbird
end
