include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cno.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cva.mm"
include "cmul.mm"
include "cle.mm"
include "wral.mm"
include "wa.mm"
include "cr.mm"
include "wrex.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "w3a.mm"
include "cdj3lem1.mm"
include "cph.mm"
include "cdj3lem2b.mm"
include "sylibr.mm"
include "cdj3lem3b.mm"
include "3jca.mm"
include "weq.mm"
include "breq2.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "bitri.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "wcel.mm"
include "an4.mm"
include "wi.mm"
include "addgt0.mm"
include "ex.mm"
include "adantl.mm"
include "shsvai.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "rspcv.mm"
include "anim12d.mm"
include "syl.mm"
include "chil.mm"
include "sheli.mm"
include "normcl.mm"
include "anim12i.mm"
include "hvaddcl.mm"
include "syl2an.mm"
include "remulcl.mm"
include "sylan2.mm"
include "adantlr.mm"
include "adantll.mm"
include "le2add.mm"
include "syl12anc.mm"
include "wb.mm"
include "cdj3lem2.mm"
include "breq1d.mm"
include "cdj3lem3.mm"
include "3expa.mm"
include "ancoms.mm"
include "cc.mm"
include "recn.mm"
include "recnd.mm"
include "adddir.mm"
include "syl3an.mm"
include "3imtr4d.mm"
include "syld.mm"
include "ralrimdvva.mm"
include "readdcl.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "cbvral2v.mm"
include "2ralbidv.mm"
include "syl5bb.mm"
include "rspcev.mm"
include "syl2and.mm"
include "syl5bi.mm"
include "rexlimdvva.mm"
include "3impib.mm"
include "impbii.mm"

theorem cdj3i
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vt: setvar t
  let vh: setvar h
  let vf: setvar f
  let vg: setvar g
  assume cdj3.1: |- A e. SH
  assume cdj3.2: |- B e. SH
  assume cdj3.3: |- S = ( x e. ( A +H B ) |-> ( iota_ z e. A E. w e. B x = ( z +h w ) ) )
  assume cdj3.4: |- T = ( x e. ( A +H B ) |-> ( iota_ w e. B E. z e. A x = ( z +h w ) ) )
  assume cdj3.5: |- ( ph <-> E. v e. RR ( 0 < v /\ A. u e. ( A +H B ) ( normh ` ( S ` u ) ) <_ ( v x. ( normh ` u ) ) ) )
  assume cdj3.6: |- ( ps <-> E. v e. RR ( 0 < v /\ A. u e. ( A +H B ) ( normh ` ( T ` u ) ) <_ ( v x. ( normh ` u ) ) ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint A w
  disjoint u v
  disjoint A v
  disjoint A u
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint S v
  disjoint S u
  disjoint T v
  disjoint T u
  disjoint t x
  disjoint h x
  disjoint f x
  disjoint g x
  disjoint t y
  disjoint h y
  disjoint f y
  disjoint g y
  disjoint t z
  disjoint h z
  disjoint f z
  disjoint g z
  disjoint t w
  disjoint h w
  disjoint f w
  disjoint g w
  disjoint t v
  disjoint h v
  disjoint f v
  disjoint g v
  disjoint t u
  disjoint h u
  disjoint f u
  disjoint g u
  disjoint h t
  disjoint f t
  disjoint g t
  disjoint A t
  disjoint f h
  disjoint g h
  disjoint A h
  disjoint f g
  disjoint A f
  disjoint A g
  disjoint B t
  disjoint B h
  disjoint B f
  disjoint B g
  disjoint S t
  disjoint S h
  disjoint S f
  disjoint S g
  disjoint T t
  disjoint T h
  disjoint T f
  disjoint T g
  assert |- ( E. v e. RR ( 0 < v /\ A. x e. A A. y e. B ( ( normh ` x ) + ( normh ` y ) ) <_ ( v x. ( normh ` ( x +h y ) ) ) ) <-> ( ( A i^i B ) = 0H /\ ph /\ ps ) )

  proof
    cc0
    vv
    cv
    #
    clt
    wbr
    #
    vx
    cv
    #
    cno
    cfv
    #
    vy
    cv
    #
    cno
    cfv
    #
    caddc
    co
    #
    @0
    @2
    @4
    cva
    co
    #
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    wa
    #
    vv
    cr
    wrex
    #
    cA
    cB
    cin
    c0h
    wceq
    #
    wph
    wps
    w3a
    @13
    @14
    wph
    wps
    vv
    vx
    vy
    cA
    cB
    cdj3.1
    cdj3.2
    cdj3lem1
    @13
    @1
    vu
    cv
    #
    cS
    cfv
    #
    cno
    cfv
    #
    @0
    @15
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vu
    cA
    cB
    cph
    co
    #
    wral
    #
    wa
    #
    vv
    cr
    wrex
    #
    wph
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cS
    cdj3.1
    cdj3.2
    cdj3.3
    cdj3lem2b
    cdj3.5
    sylibr
    @13
    @1
    @15
    cT
    cfv
    #
    cno
    cfv
    #
    @19
    cle
    wbr
    #
    vu
    @21
    wral
    #
    wa
    #
    vv
    cr
    wrex
    #
    wps
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cT
    cdj3.1
    cdj3.2
    cdj3.4
    cdj3lem3b
    cdj3.6
    sylibr
    3jca
    @14
    wph
    wps
    @13
    wph
    wps
    wa
    #
    cc0
    vf
    cv
    #
    clt
    wbr
    #
    @17
    @32
    @18
    cmul
    co
    #
    cle
    wbr
    #
    vu
    @21
    wral
    #
    wa
    #
    cc0
    vg
    cv
    #
    clt
    wbr
    #
    @26
    @38
    @18
    cmul
    co
    #
    cle
    wbr
    #
    vu
    @21
    wral
    #
    wa
    #
    wa
    #
    vg
    cr
    wrex
    vf
    cr
    wrex
    #
    @14
    @13
    @31
    @37
    vf
    cr
    wrex
    #
    @43
    vg
    cr
    wrex
    #
    wa
    @45
    wph
    @46
    wps
    @47
    wph
    @24
    @46
    cdj3.5
    @23
    @37
    vv
    vf
    cr
    vv
    vf
    weq
    #
    @1
    @33
    @22
    @36
    @0
    @32
    cc0
    clt
    breq2
    @48
    @20
    @35
    vu
    @21
    @48
    @19
    @34
    @17
    cle
    @0
    @32
    @18
    cmul
    oveq1
    breq2d
    ralbidv
    anbi12d
    cbvrexv
    bitri
    wps
    @30
    @47
    cdj3.6
    @29
    @43
    vv
    vg
    cr
    vv
    vg
    weq
    #
    @1
    @39
    @28
    @42
    @0
    @38
    cc0
    clt
    breq2
    @49
    @27
    @41
    vu
    @21
    @49
    @19
    @40
    @26
    cle
    @0
    @38
    @18
    cmul
    oveq1
    breq2d
    ralbidv
    anbi12d
    cbvrexv
    bitri
    anbi12i
    @37
    @43
    vf
    vg
    cr
    cr
    reeanv
    bitr4i
    @14
    @44
    @13
    vf
    vg
    cr
    cr
    @44
    @33
    @39
    wa
    #
    @36
    @42
    wa
    #
    wa
    @14
    @32
    cr
    wcel
    #
    @38
    cr
    wcel
    #
    wa
    #
    wa
    #
    @13
    @33
    @36
    @39
    @42
    an4
    @55
    @50
    cc0
    @32
    @38
    caddc
    co
    #
    clt
    wbr
    #
    @51
    vt
    cv
    #
    cno
    cfv
    #
    vh
    cv
    #
    cno
    cfv
    #
    caddc
    co
    #
    @56
    @58
    @60
    cva
    co
    #
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vh
    cB
    wral
    vt
    cA
    wral
    #
    @13
    @54
    @50
    @57
    wi
    @14
    @54
    @50
    @57
    @32
    @38
    addgt0
    ex
    adantl
    @55
    @51
    @66
    vt
    vh
    cA
    cB
    @55
    @58
    cA
    wcel
    #
    @60
    cB
    wcel
    #
    wa
    #
    wa
    #
    @51
    @63
    cS
    cfv
    #
    cno
    cfv
    #
    @32
    @64
    cmul
    co
    #
    cle
    wbr
    #
    @63
    cT
    cfv
    #
    cno
    cfv
    #
    @38
    @64
    cmul
    co
    #
    cle
    wbr
    #
    wa
    #
    @66
    @70
    @51
    @80
    wi
    #
    @55
    @70
    @63
    @21
    wcel
    #
    @81
    cA
    cB
    @58
    @60
    cdj3.1
    cdj3.2
    shsvai
    @82
    @36
    @75
    @42
    @79
    @35
    @75
    vu
    @63
    @21
    @15
    @63
    wceq
    #
    @17
    @73
    @34
    @74
    cle
    @83
    @16
    @72
    cno
    @15
    @63
    cS
    fveq2
    fveq2d
    @83
    @18
    @64
    @32
    cmul
    @15
    @63
    cno
    fveq2
    #
    oveq2d
    breq12d
    rspcv
    @41
    @79
    vu
    @63
    @21
    @83
    @26
    @77
    @40
    @78
    cle
    @83
    @25
    @76
    cno
    @15
    @63
    cT
    fveq2
    fveq2d
    @83
    @18
    @64
    @38
    cmul
    @84
    oveq2d
    breq12d
    rspcv
    anim12d
    syl
    adantl
    @71
    @59
    @74
    cle
    wbr
    #
    @61
    @78
    cle
    wbr
    #
    wa
    #
    @62
    @74
    @78
    caddc
    co
    #
    cle
    wbr
    #
    @80
    @66
    @54
    @70
    @87
    @89
    wi
    #
    @14
    @54
    @70
    wa
    #
    @59
    cr
    wcel
    #
    @61
    cr
    wcel
    #
    wa
    #
    @74
    cr
    wcel
    #
    @78
    cr
    wcel
    #
    @90
    @70
    @94
    @54
    @68
    @92
    @69
    @93
    @68
    @58
    chil
    wcel
    #
    @92
    @58
    cA
    cdj3.1
    sheli
    #
    @58
    normcl
    syl
    @69
    @60
    chil
    wcel
    #
    @93
    @60
    cB
    cdj3.2
    sheli
    #
    @60
    normcl
    syl
    anim12i
    adantl
    @52
    @70
    @95
    @53
    @70
    @52
    @64
    cr
    wcel
    #
    @95
    @70
    @63
    chil
    wcel
    #
    @101
    @68
    @97
    @99
    @102
    @69
    @98
    @100
    @58
    @60
    hvaddcl
    syl2an
    @63
    normcl
    syl
    #
    @32
    @64
    remulcl
    sylan2
    adantlr
    @53
    @70
    @96
    @52
    @70
    @53
    @101
    @96
    @103
    @38
    @64
    remulcl
    sylan2
    adantll
    @59
    @61
    @74
    @78
    le2add
    syl12anc
    adantll
    @14
    @70
    @80
    @87
    wb
    #
    @54
    @70
    @14
    @104
    @68
    @69
    @14
    @104
    @68
    @69
    @14
    w3a
    #
    @75
    @85
    @79
    @86
    @105
    @73
    @59
    @74
    cle
    @105
    @72
    @58
    cno
    vx
    vz
    vw
    cA
    cB
    @58
    @60
    cS
    cdj3.1
    cdj3.2
    cdj3.3
    cdj3lem2
    fveq2d
    breq1d
    @105
    @77
    @61
    @78
    cle
    @105
    @76
    @60
    cno
    vx
    vz
    vw
    cA
    cB
    @58
    @60
    cT
    cdj3.1
    cdj3.2
    cdj3.4
    cdj3lem3
    fveq2d
    breq1d
    anbi12d
    3expa
    ancoms
    adantlr
    @54
    @70
    @66
    @89
    wb
    @14
    @91
    @65
    @88
    @62
    cle
    @52
    @53
    @70
    @65
    @88
    wceq
    #
    @52
    @32
    cc
    wcel
    @53
    @38
    cc
    wcel
    @70
    @64
    cc
    wcel
    @106
    @32
    recn
    @38
    recn
    @70
    @64
    @103
    recnd
    @32
    @38
    @64
    adddir
    syl3an
    3expa
    breq2d
    adantll
    3imtr4d
    syld
    ralrimdvva
    @54
    @57
    @67
    wa
    #
    @13
    wi
    #
    @14
    @54
    @56
    cr
    wcel
    #
    @108
    @32
    @38
    readdcl
    @109
    @107
    @13
    @12
    @107
    vv
    @56
    cr
    @0
    @56
    wceq
    #
    @1
    @57
    @11
    @67
    @0
    @56
    cc0
    clt
    breq2
    @11
    @62
    @0
    @64
    cmul
    co
    #
    cle
    wbr
    #
    vh
    cB
    wral
    vt
    cA
    wral
    @110
    @67
    @10
    @112
    @59
    @5
    caddc
    co
    #
    @0
    @58
    @4
    cva
    co
    #
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    vx
    vy
    vt
    vh
    cA
    cB
    vx
    vt
    weq
    #
    @6
    @113
    @9
    @116
    cle
    @117
    @3
    @59
    @5
    caddc
    @2
    @58
    cno
    fveq2
    oveq1d
    @117
    @8
    @115
    @0
    cmul
    @117
    @7
    @114
    cno
    @2
    @58
    @4
    cva
    oveq1
    fveq2d
    oveq2d
    breq12d
    vy
    vh
    weq
    #
    @113
    @62
    @116
    @111
    cle
    @118
    @5
    @61
    @59
    caddc
    @4
    @60
    cno
    fveq2
    oveq2d
    @118
    @115
    @64
    @0
    cmul
    @118
    @114
    @63
    cno
    @4
    @60
    @58
    cva
    oveq2
    fveq2d
    oveq2d
    breq12d
    cbvral2v
    @110
    @112
    @66
    vt
    vh
    cA
    cB
    @110
    @111
    @65
    @62
    cle
    @0
    @56
    @64
    cmul
    oveq1
    breq2d
    2ralbidv
    syl5bb
    anbi12d
    rspcev
    ex
    syl
    adantl
    syl2and
    syl5bi
    rexlimdvva
    syl5bi
    3impib
    impbii
end
