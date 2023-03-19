include "wor.mm"
include "wa.mm"
include "cxp.mm"
include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "w3o.mm"
include "wral.mm"
include "sopo.mm"
include "poxp.mm"
include "syl2an.mm"
include "wcel.mm"
include "cop.mm"
include "wex.mm"
include "wi.mm"
include "elxp.mm"
include "wo.mm"
include "wn.mm"
include "ioran.mm"
include "ianor.mm"
include "anbi2i.mm"
include "bitri.mm"
include "anbi12i.mm"
include "solin.mm"
include "3orass.mm"
include "df-or.mm"
include "sylib.mm"
include "orim2d.mm"
include "im2anan9.mm"
include "pm2.53.mm"
include "orc.mm"
include "syl6.mm"
include "adantr.mm"
include "orel1.mm"
include "anim2d.mm"
include "imor.mm"
include "biimpri.mm"
include "com12.mm"
include "equcomi.mm"
include "anim1i.mm"
include "olcd.mm"
include "ex.mm"
include "syld.mm"
include "a1d.mm"
include "jaoi.mm"
include "imp.mm"
include "syl6com.mm"
include "jaod.mm"
include "impd.mm"
include "syl5bi.mm"
include "df-3or.mm"
include "sylibr.mm"
include "pm3.2.mm"
include "ad2ant2l.mm"
include "idd.mm"
include "simpr.mm"
include "ancomd.mm"
include "3orim123d.mm"
include "mpd.mm"
include "an4s.mm"
include "expcom.mm"
include "breq12.mm"
include "eqeq12.mm"
include "wb.mm"
include "ancoms.mm"
include "3orbi123d.mm"
include "xporderlem.mm"
include "vex.mm"
include "opth.mm"
include "3orbi123i.mm"
include "syl6bb.mm"
include "biimprcd.mm"
include "com3r.mm"
include "exlimivv.mm"
include "syl2anb.mm"
include "ralrimivv.mm"
include "df-so.mm"
include "sylanbrc.mm"

theorem soxp
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vt: setvar t
  let vu: setvar u
  assume soxp.1: |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) ) /\ ( ( 1st ` x ) R ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) }

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A t
  disjoint A u
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a t
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b d
  disjoint b t
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint c d
  disjoint c t
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint d t
  disjoint d u
  disjoint d x
  disjoint d y
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint u x
  disjoint u y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B t
  disjoint B u
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint R t
  disjoint R u
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S t
  disjoint S u
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint T t
  disjoint T u
  assert |- ( ( R Or A /\ S Or B ) -> T Or ( A X. B ) )

  proof
    cA
    cR
    wor
    #
    cB
    cS
    wor
    #
    wa
    #
    cA
    cB
    cxp
    #
    cT
    wpo
    #
    vt
    cv
    #
    vu
    cv
    #
    cT
    wbr
    #
    @5
    @6
    wceq
    #
    @6
    @5
    cT
    wbr
    #
    w3o
    #
    vu
    @3
    wral
    vt
    @3
    wral
    @3
    cT
    wor
    @0
    cA
    cR
    wpo
    cB
    cS
    wpo
    @4
    @1
    cA
    cR
    sopo
    cB
    cS
    sopo
    vx
    vy
    cA
    cB
    cR
    cS
    cT
    soxp.1
    poxp
    syl2an
    @2
    @10
    vt
    vu
    @3
    @3
    @5
    @3
    wcel
    #
    @6
    @3
    wcel
    #
    wa
    @2
    @10
    @11
    @5
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    wceq
    #
    @13
    cA
    wcel
    #
    @14
    cB
    wcel
    #
    wa
    #
    wa
    #
    vb
    wex
    va
    wex
    #
    @6
    vc
    cv
    #
    vd
    cv
    #
    cop
    #
    wceq
    #
    @22
    cA
    wcel
    #
    @23
    cB
    wcel
    #
    wa
    #
    wa
    #
    vd
    wex
    vc
    wex
    #
    @2
    @10
    wi
    #
    @12
    va
    vb
    @5
    cA
    cB
    elxp
    vc
    vd
    @6
    cA
    cB
    elxp
    @21
    @30
    @31
    @20
    @30
    @31
    wi
    va
    vb
    @30
    @20
    @31
    @29
    @20
    @31
    wi
    vc
    vd
    @20
    @29
    @31
    @16
    @25
    @19
    @28
    @31
    @16
    @25
    wa
    #
    @19
    @28
    wa
    #
    @31
    @33
    @2
    @32
    @10
    @33
    @2
    @17
    @26
    wa
    #
    @18
    @27
    wa
    #
    wa
    #
    @13
    @22
    cR
    wbr
    #
    @13
    @22
    wceq
    #
    @14
    @23
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    @38
    @14
    @23
    wceq
    #
    wa
    #
    @26
    @17
    wa
    #
    @27
    @18
    wa
    #
    wa
    #
    @22
    @13
    cR
    wbr
    #
    @22
    @13
    wceq
    #
    @23
    @14
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    w3o
    #
    @32
    @10
    wi
    @17
    @26
    @18
    @27
    @2
    @54
    wi
    @2
    @36
    @54
    @0
    @34
    @1
    @35
    @54
    @0
    @34
    wa
    #
    @1
    @35
    wa
    #
    wa
    #
    @41
    @44
    @52
    w3o
    #
    @54
    @57
    @41
    @44
    wo
    #
    wn
    #
    @52
    wi
    #
    @58
    @60
    @37
    wn
    #
    @38
    wn
    #
    @39
    wn
    #
    wo
    #
    wa
    #
    @63
    @43
    wn
    #
    wo
    #
    wa
    #
    @57
    @52
    @60
    @41
    wn
    #
    @44
    wn
    #
    wa
    @69
    @41
    @44
    ioran
    @70
    @66
    @71
    @68
    @70
    @62
    @40
    wn
    #
    wa
    @66
    @37
    @40
    ioran
    @72
    @65
    @62
    @38
    @39
    ianor
    anbi2i
    bitri
    @38
    @43
    ianor
    anbi12i
    bitri
    @57
    @66
    @68
    @52
    @57
    @66
    @38
    @48
    wo
    #
    @63
    @43
    @50
    wo
    #
    wo
    #
    wa
    #
    @68
    @52
    wi
    @55
    @62
    @73
    @56
    @65
    @75
    @55
    @37
    @38
    @48
    w3o
    #
    @62
    @73
    wi
    #
    cA
    @13
    @22
    cR
    solin
    @77
    @37
    @73
    wo
    @78
    @37
    @38
    @48
    3orass
    @37
    @73
    df-or
    bitri
    sylib
    @56
    @64
    @74
    @63
    @56
    @39
    @43
    @50
    w3o
    #
    @64
    @74
    wi
    #
    cB
    @14
    @23
    cS
    solin
    @79
    @39
    @74
    wo
    @80
    @39
    @43
    @50
    3orass
    @39
    @74
    df-or
    bitri
    sylib
    orim2d
    im2anan9
    @76
    @63
    @52
    @67
    @73
    @63
    @52
    wi
    @75
    @73
    @63
    @48
    @52
    @38
    @48
    pm2.53
    @48
    @51
    orc
    #
    syl6
    adantr
    @67
    @76
    @73
    @63
    @50
    wo
    #
    wa
    @52
    @67
    @75
    @82
    @73
    @67
    @74
    @50
    @63
    @43
    @50
    orel1
    orim2d
    anim2d
    @73
    @82
    @52
    @38
    @82
    @52
    wi
    @48
    @38
    @82
    @50
    @52
    @82
    @38
    @50
    @38
    @50
    wi
    @82
    @38
    @50
    imor
    biimpri
    com12
    @38
    @50
    @52
    @38
    @50
    wa
    @51
    @48
    @38
    @49
    @50
    va
    vc
    equcomi
    anim1i
    olcd
    ex
    syld
    @48
    @52
    @82
    @81
    a1d
    jaoi
    imp
    syl6com
    jaod
    syl6
    impd
    syl5bi
    @58
    @59
    @52
    wo
    @61
    @41
    @44
    @52
    df-3or
    @59
    @52
    df-or
    bitri
    sylibr
    @57
    @41
    @42
    @44
    @44
    @52
    @53
    @34
    @35
    @41
    @42
    wi
    @0
    @1
    @36
    @41
    pm3.2
    ad2ant2l
    @57
    @44
    idd
    @55
    @45
    @46
    @52
    @53
    wi
    @56
    @55
    @17
    @26
    @0
    @34
    simpr
    ancomd
    @56
    @18
    @27
    @1
    @35
    simpr
    ancomd
    @47
    @52
    pm3.2
    syl2an
    3orim123d
    mpd
    an4s
    expcom
    an4s
    @32
    @10
    @54
    @32
    @10
    @15
    @24
    cT
    wbr
    #
    @15
    @24
    wceq
    #
    @24
    @15
    cT
    wbr
    #
    w3o
    @54
    @32
    @7
    @83
    @8
    @84
    @9
    @85
    @5
    @15
    @6
    @24
    cT
    breq12
    @5
    @15
    @6
    @24
    eqeq12
    @25
    @16
    @9
    @85
    wb
    @6
    @24
    @5
    @15
    cT
    breq12
    ancoms
    3orbi123d
    @83
    @42
    @84
    @44
    @85
    @53
    vx
    vy
    cA
    cB
    cR
    cS
    cT
    va
    vb
    vc
    vd
    soxp.1
    xporderlem
    @13
    @14
    @22
    @23
    va
    vex
    vb
    vex
    opth
    vx
    vy
    cA
    cB
    cR
    cS
    cT
    vc
    vd
    va
    vb
    soxp.1
    xporderlem
    3orbi123i
    syl6bb
    biimprcd
    syl6
    com3r
    imp
    an4s
    expcom
    exlimivv
    com12
    exlimivv
    imp
    syl2anb
    com12
    ralrimivv
    vt
    vu
    @3
    cT
    df-so
    sylanbrc
end
