include "wpo.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "cxp.mm"
include "wral.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "elxp.mm"
include "w3a.mm"
include "3an6.mm"
include "weq.mm"
include "wo.mm"
include "poirr.mm"
include "ex.mm"
include "intnand.mm"
include "im2anan9.mm"
include "ioran.mm"
include "syl6ibr.mm"
include "imp.mm"
include "3ad2antr1.mm"
include "an4.mm"
include "potr.mm"
include "3impia.mm"
include "orcd.mm"
include "3expia.mm"
include "expdimp.mm"
include "breq2.mm"
include "biimpa.mm"
include "expcom.mm"
include "adantrd.mm"
include "adantl.mm"
include "jaod.mm"
include "anim2d.mm"
include "orim2d.mm"
include "breq1.mm"
include "equequ1.mm"
include "anbi1d.mm"
include "orbi12d.mm"
include "imbi2d.mm"
include "syl5ibr.mm"
include "expd.mm"
include "com12.mm"
include "impd.mm"
include "jaao.mm"
include "an4s.mm"
include "sylan2b.mm"
include "biimpi.mm"
include "3adant2.mm"
include "jctild.mm"
include "adantld.mm"
include "syl5bi.mm"
include "jca.mm"
include "wb.mm"
include "breq12.mm"
include "anidms.mm"
include "notbid.mm"
include "3ad2ant1.mm"
include "3adant3.mm"
include "3adant1.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "xporderlem.mm"
include "notbii.mm"
include "anbi12i.mm"
include "imbi12i.mm"
include "syl6bb.mm"
include "expcomd.mm"
include "sylbi.mm"
include "3exp.mm"
include "com3l.mm"
include "exlimivv.mm"
include "3imp.mm"
include "syl3anb.mm"
include "com3r.mm"
include "ralrimiv.mm"
include "ralrimivva.mm"
include "df-po.mm"
include "sylibr.mm"

theorem poxp
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
  let ve: setvar e
  let vf: setvar f
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  assume poxp.1: |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) ) /\ ( ( 1st ` x ) R ( 1st ` y ) \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) }

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
  disjoint A e
  disjoint A f
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c y
  disjoint d e
  disjoint d f
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint e f
  disjoint e t
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint e y
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B t
  disjoint B u
  disjoint B v
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint R t
  disjoint R u
  disjoint R v
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S e
  disjoint S f
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint T e
  disjoint T f
  disjoint T t
  disjoint T u
  disjoint T v
  assert |- ( ( R Po A /\ S Po B ) -> T Po ( A X. B ) )

  proof
    cA
    cR
    wpo
    #
    cB
    cS
    wpo
    #
    wa
    #
    vt
    cv
    #
    @3
    cT
    wbr
    #
    wn
    #
    @3
    vu
    cv
    #
    cT
    wbr
    #
    @6
    vv
    cv
    #
    cT
    wbr
    #
    wa
    #
    @3
    @8
    cT
    wbr
    #
    wi
    #
    wa
    #
    vv
    cA
    cB
    cxp
    #
    wral
    #
    vu
    @14
    wral
    vt
    @14
    wral
    @14
    cT
    wpo
    @2
    @15
    vt
    vu
    @14
    @14
    @2
    @3
    @14
    wcel
    #
    @6
    @14
    wcel
    #
    wa
    #
    wa
    @13
    vv
    @14
    @2
    @18
    @8
    @14
    wcel
    #
    @13
    wi
    @18
    @19
    @2
    @13
    @16
    @17
    @19
    @2
    @13
    wi
    #
    @16
    @3
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
    @21
    cA
    wcel
    #
    @22
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
    @17
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
    @30
    cA
    wcel
    #
    @31
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
    @19
    @8
    ve
    cv
    #
    vf
    cv
    #
    cop
    #
    wceq
    #
    @39
    cA
    wcel
    #
    @40
    cB
    wcel
    #
    wa
    #
    wa
    #
    vf
    wex
    ve
    wex
    #
    @20
    va
    vb
    @3
    cA
    cB
    elxp
    vc
    vd
    @6
    cA
    cB
    elxp
    ve
    vf
    @8
    cA
    cB
    elxp
    @29
    @38
    @47
    @20
    @28
    @38
    @47
    @20
    wi
    wi
    va
    vb
    @47
    @28
    @38
    @20
    @46
    @28
    @38
    @20
    wi
    wi
    ve
    vf
    @38
    @46
    @28
    @20
    @37
    @46
    @28
    @20
    wi
    wi
    vc
    vd
    @28
    @37
    @46
    @20
    @28
    @37
    @46
    @20
    @28
    @37
    @46
    w3a
    @24
    @33
    @42
    w3a
    #
    @27
    @36
    @45
    w3a
    #
    wa
    @20
    @24
    @27
    @33
    @36
    @42
    @45
    3an6
    @48
    @49
    @20
    @48
    @2
    @49
    @13
    @2
    @49
    wa
    #
    @13
    @48
    @25
    @25
    wa
    @26
    @26
    wa
    wa
    #
    @21
    @21
    cR
    wbr
    #
    va
    va
    weq
    #
    @22
    @22
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    wn
    #
    @25
    @34
    wa
    @26
    @35
    wa
    wa
    #
    @21
    @30
    cR
    wbr
    #
    va
    vc
    weq
    #
    @22
    @31
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    @34
    @43
    wa
    @35
    @44
    wa
    wa
    #
    @30
    @39
    cR
    wbr
    #
    vc
    ve
    weq
    #
    @31
    @40
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    wa
    #
    @25
    @43
    wa
    @26
    @44
    wa
    wa
    #
    @21
    @39
    cR
    wbr
    #
    va
    ve
    weq
    #
    @22
    @40
    cS
    wbr
    #
    wa
    #
    wo
    #
    wa
    #
    wi
    #
    wa
    #
    @50
    @58
    @81
    @2
    @36
    @27
    @58
    @45
    @2
    @27
    wa
    @56
    @51
    @2
    @27
    @56
    wn
    #
    @2
    @27
    @52
    wn
    #
    @55
    wn
    #
    wa
    @83
    @0
    @25
    @84
    @1
    @26
    @85
    @0
    @25
    @84
    cA
    @21
    cR
    poirr
    ex
    @1
    @26
    @85
    @1
    @26
    wa
    @54
    @53
    cB
    @22
    cS
    poirr
    intnand
    ex
    im2anan9
    @52
    @55
    ioran
    syl6ibr
    imp
    intnand
    3ad2antr1
    @73
    @59
    @66
    wa
    #
    @64
    @71
    wa
    #
    wa
    @50
    @80
    @59
    @64
    @66
    @71
    an4
    @50
    @87
    @80
    @86
    @50
    @87
    @79
    @74
    @49
    @2
    @25
    @34
    @43
    w3a
    #
    @26
    @35
    @44
    w3a
    #
    wa
    @87
    @79
    wi
    #
    @25
    @26
    @34
    @35
    @43
    @44
    3an6
    @0
    @88
    @1
    @89
    @90
    @0
    @88
    wa
    #
    @1
    @89
    wa
    #
    wa
    @64
    @71
    @79
    @91
    @60
    @71
    @79
    wi
    #
    @92
    @63
    @91
    @60
    @93
    @91
    @60
    wa
    @67
    @79
    @70
    @91
    @60
    @67
    @79
    @0
    @88
    @60
    @67
    wa
    #
    @79
    @0
    @88
    @94
    w3a
    @75
    @78
    @0
    @88
    @94
    @75
    cA
    @21
    @30
    @39
    cR
    potr
    3impia
    orcd
    3expia
    expdimp
    @60
    @70
    @79
    wi
    @91
    @60
    @68
    @79
    @69
    @68
    @60
    @79
    @68
    @60
    wa
    @75
    @78
    @68
    @60
    @75
    @30
    @39
    @21
    cR
    breq2
    biimpa
    orcd
    expcom
    adantrd
    adantl
    jaod
    ex
    @92
    @61
    @62
    @93
    @61
    @92
    @62
    @93
    wi
    @61
    @92
    @62
    @93
    @92
    @62
    wa
    #
    @93
    @61
    @71
    @67
    @68
    @77
    wa
    #
    wo
    #
    wi
    @95
    @70
    @96
    @67
    @95
    @69
    @77
    @68
    @92
    @62
    @69
    @77
    cB
    @22
    @31
    @40
    cS
    potr
    expdimp
    anim2d
    orim2d
    @61
    @79
    @97
    @71
    @61
    @75
    @67
    @78
    @96
    @21
    @30
    @39
    cR
    breq1
    @61
    @76
    @68
    @77
    va
    vc
    ve
    equequ1
    anbi1d
    orbi12d
    imbi2d
    syl5ibr
    expd
    com12
    impd
    jaao
    impd
    an4s
    sylan2b
    @49
    @74
    @2
    @27
    @45
    @74
    @36
    @27
    @45
    wa
    @74
    @25
    @26
    @43
    @44
    an4
    biimpi
    3adant2
    adantl
    jctild
    adantld
    syl5bi
    jca
    @48
    @13
    @23
    @23
    cT
    wbr
    #
    wn
    #
    @23
    @32
    cT
    wbr
    #
    @32
    @41
    cT
    wbr
    #
    wa
    #
    @23
    @41
    cT
    wbr
    #
    wi
    #
    wa
    @82
    @48
    @5
    @99
    @12
    @104
    @24
    @33
    @5
    @99
    wb
    @42
    @24
    @4
    @98
    @24
    @4
    @98
    wb
    @3
    @23
    @3
    @23
    cT
    breq12
    anidms
    notbid
    3ad2ant1
    @48
    @10
    @102
    @11
    @103
    @48
    @7
    @100
    @9
    @101
    @24
    @33
    @7
    @100
    wb
    @42
    @3
    @23
    @6
    @32
    cT
    breq12
    3adant3
    @33
    @42
    @9
    @101
    wb
    @24
    @6
    @32
    @8
    @41
    cT
    breq12
    3adant1
    anbi12d
    @24
    @42
    @11
    @103
    wb
    @33
    @3
    @23
    @8
    @41
    cT
    breq12
    3adant2
    imbi12d
    anbi12d
    @99
    @58
    @104
    @81
    @98
    @57
    vx
    vy
    cA
    cB
    cR
    cS
    cT
    va
    vb
    va
    vb
    poxp.1
    xporderlem
    notbii
    @102
    @73
    @103
    @80
    @100
    @65
    @101
    @72
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
    poxp.1
    xporderlem
    vx
    vy
    cA
    cB
    cR
    cS
    cT
    vc
    vd
    ve
    vf
    poxp.1
    xporderlem
    anbi12i
    vx
    vy
    cA
    cB
    cR
    cS
    cT
    va
    vb
    ve
    vf
    poxp.1
    xporderlem
    imbi12i
    anbi12i
    syl6bb
    syl5ibr
    expcomd
    imp
    sylbi
    3exp
    com3l
    exlimivv
    com3l
    exlimivv
    com3l
    exlimivv
    3imp
    syl3anb
    3expia
    com3r
    imp
    ralrimiv
    ralrimivva
    vt
    vu
    vv
    @14
    cT
    df-po
    sylibr
end
