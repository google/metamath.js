include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wrex.mm"
include "citv.mm"
include "cfv.mm"
include "wsbc.mm"
include "cds.mm"
include "cbs.mm"
include "copab.mm"
include "cstrkg.mm"
include "cafs.mm"
include "cvv.mm"
include "cmpt.mm"
include "df-afs.mm"
include "a1i.mm"
include "wb.mm"
include "simp1.mm"
include "eqcomd.mm"
include "adantr.mm"
include "ad7antr.mm"
include "simp3.mm"
include "ad8antr.mm"
include "oveqd.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "simp2.mm"
include "eqeq12d.mm"
include "3anbi123d.mm"
include "3anbi3d.mm"
include "rexeqbidva.mm"
include "sbcie3s.mm"
include "adantl.mm"
include "opabbidv.mm"
include "cxp.mm"
include "df-xp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "eqeltrri.mm"
include "3simpa.mm"
include "reximi.mm"
include "simpr.mm"
include "opelxpi.mm"
include "simp-7r.mm"
include "simp-6r.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "simp-5r.mm"
include "simp-4r.mm"
include "simpllr.mm"
include "simplr.mm"
include "anim12dan.mm"
include "ex.mm"
include "rexlimdva.mm"
include "rexlimivv.mm"
include "syl.mm"
include "ssopab2i.mm"
include "ssexi.mm"
include "fvmptd.mm"

theorem afsval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cP: class P
  let ve: setvar e
  let vf: setvar f
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vp: setvar p
  assume brafs.p: |- P = ( Base ` G )
  assume brafs.d: |- .- = ( dist ` G )
  assume brafs.i: |- I = ( Itv ` G )
  assume brafs.g: |- ( ph -> G e. TarskiG )

  disjoint e f
  disjoint G e
  disjoint G f
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint I a
  disjoint b c
  disjoint b d
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint I b
  disjoint c d
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint I c
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint I d
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint x y
  disjoint x z
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint a e
  disjoint a f
  disjoint P a
  disjoint b e
  disjoint b f
  disjoint P b
  disjoint c e
  disjoint c f
  disjoint P c
  disjoint d e
  disjoint d f
  disjoint P d
  disjoint e w
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint P e
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint P f
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint .- a
  disjoint .- b
  disjoint .- c
  disjoint .- d
  disjoint .- w
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint e ph
  disjoint f ph
  disjoint e g
  disjoint e h
  disjoint e i
  disjoint e p
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f p
  disjoint g h
  disjoint g i
  disjoint g p
  disjoint G g
  disjoint h i
  disjoint h p
  disjoint G h
  disjoint i p
  disjoint G i
  disjoint G p
  disjoint a g
  disjoint a h
  disjoint a i
  disjoint a p
  disjoint b g
  disjoint b h
  disjoint b i
  disjoint b p
  disjoint c g
  disjoint c h
  disjoint c i
  disjoint c p
  disjoint d g
  disjoint d h
  disjoint d i
  disjoint d p
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint I g
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint I h
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint I i
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint I p
  disjoint P g
  disjoint P h
  disjoint P i
  disjoint P p
  disjoint .- g
  disjoint .- h
  disjoint .- i
  disjoint .- p
  disjoint g ph
  assert |- ( ph -> ( AFS ` G ) = { <. e , f >. | E. a e. P E. b e. P E. c e. P E. d e. P E. x e. P E. y e. P E. z e. P E. w e. P ( e = <. <. a , b >. , <. c , d >. >. /\ f = <. <. x , y >. , <. z , w >. >. /\ ( ( b e. ( a I c ) /\ y e. ( x I z ) ) /\ ( ( a .- b ) = ( x .- y ) /\ ( b .- c ) = ( y .- z ) ) /\ ( ( a .- d ) = ( x .- w ) /\ ( b .- d ) = ( y .- w ) ) ) ) } )

  proof
    wph
    vg
    cG
    ve
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    vc
    cv
    #
    vd
    cv
    #
    cop
    #
    cop
    #
    wceq
    #
    vf
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    cop
    #
    wceq
    #
    @2
    @1
    @4
    vi
    cv
    #
    co
    #
    wcel
    #
    @11
    @10
    @13
    @18
    co
    #
    wcel
    #
    wa
    #
    @1
    @2
    vh
    cv
    #
    co
    #
    @10
    @11
    @24
    co
    #
    wceq
    #
    @2
    @4
    @24
    co
    #
    @11
    @13
    @24
    co
    #
    wceq
    #
    wa
    #
    @1
    @5
    @24
    co
    #
    @10
    @14
    @24
    co
    #
    wceq
    #
    @2
    @5
    @24
    co
    #
    @11
    @14
    @24
    co
    #
    wceq
    #
    wa
    #
    w3a
    #
    w3a
    #
    vw
    vp
    cv
    #
    wrex
    #
    vz
    @41
    wrex
    #
    vy
    @41
    wrex
    #
    vx
    @41
    wrex
    #
    vd
    @41
    wrex
    #
    vc
    @41
    wrex
    #
    vb
    @41
    wrex
    #
    va
    @41
    wrex
    #
    vi
    vg
    cv
    #
    citv
    cfv
    wsbc
    vh
    @50
    cds
    cfv
    wsbc
    vp
    @50
    cbs
    cfv
    wsbc
    #
    ve
    vf
    copab
    #
    @8
    @17
    @2
    @1
    @4
    cI
    co
    #
    wcel
    #
    @11
    @10
    @13
    cI
    co
    #
    wcel
    #
    wa
    #
    @1
    @2
    c.mi
    co
    #
    @10
    @11
    c.mi
    co
    #
    wceq
    #
    @2
    @4
    c.mi
    co
    #
    @11
    @13
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @1
    @5
    c.mi
    co
    #
    @10
    @14
    c.mi
    co
    #
    wceq
    #
    @2
    @5
    c.mi
    co
    #
    @11
    @14
    c.mi
    co
    #
    wceq
    #
    wa
    #
    w3a
    #
    w3a
    #
    vw
    cP
    wrex
    #
    vz
    cP
    wrex
    #
    vy
    cP
    wrex
    #
    vx
    cP
    wrex
    #
    vd
    cP
    wrex
    #
    vc
    cP
    wrex
    #
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    #
    ve
    vf
    copab
    #
    cstrkg
    cafs
    cvv
    cafs
    vg
    cstrkg
    @52
    cmpt
    wceq
    wph
    vx
    vy
    vz
    vw
    ve
    vf
    vg
    vh
    vi
    vp
    va
    vb
    vc
    vd
    df-afs
    a1i
    wph
    @50
    cG
    wceq
    #
    wa
    @51
    @81
    ve
    vf
    @83
    @51
    @81
    wb
    wph
    @81
    @49
    vg
    cP
    c.mi
    cI
    cbs
    cds
    citv
    cG
    vp
    vh
    vi
    brafs.p
    brafs.d
    brafs.i
    @41
    cP
    wceq
    #
    @24
    c.mi
    wceq
    #
    @18
    cI
    wceq
    #
    w3a
    #
    @80
    @48
    va
    cP
    @41
    @87
    @41
    cP
    @84
    @85
    @86
    simp1
    eqcomd
    #
    @87
    @1
    cP
    wcel
    #
    wa
    #
    @79
    @47
    vb
    cP
    @41
    @87
    cP
    @41
    wceq
    #
    @89
    @88
    adantr
    #
    @90
    @2
    cP
    wcel
    #
    wa
    #
    @78
    @46
    vc
    cP
    @41
    @90
    @91
    @93
    @92
    adantr
    #
    @94
    @4
    cP
    wcel
    #
    wa
    #
    @77
    @45
    vd
    cP
    @41
    @94
    @91
    @96
    @95
    adantr
    #
    @97
    @5
    cP
    wcel
    #
    wa
    #
    @76
    @44
    vx
    cP
    @41
    @97
    @91
    @99
    @98
    adantr
    #
    @100
    @10
    cP
    wcel
    #
    wa
    #
    @75
    @43
    vy
    cP
    @41
    @100
    @91
    @102
    @101
    adantr
    #
    @103
    @11
    cP
    wcel
    #
    wa
    #
    @74
    @42
    vz
    cP
    @41
    @103
    @91
    @105
    @104
    adantr
    @106
    @13
    cP
    wcel
    #
    wa
    #
    @73
    @40
    vw
    cP
    @41
    @87
    @91
    @89
    @93
    @96
    @99
    @102
    @105
    @107
    @88
    ad7antr
    @108
    @14
    cP
    wcel
    #
    wa
    #
    @72
    @39
    @8
    @17
    @110
    @57
    @23
    @64
    @31
    @71
    @38
    @110
    @54
    @20
    @56
    @22
    @110
    @53
    @19
    @2
    @110
    cI
    @18
    @1
    @4
    @110
    @18
    cI
    @87
    @86
    @89
    @93
    @96
    @99
    @102
    @105
    @107
    @109
    @84
    @85
    @86
    simp3
    ad8antr
    eqcomd
    #
    oveqd
    eleq2d
    @110
    @55
    @21
    @11
    @110
    cI
    @18
    @10
    @13
    @111
    oveqd
    eleq2d
    anbi12d
    @110
    @60
    @27
    @63
    @30
    @110
    @58
    @25
    @59
    @26
    @110
    c.mi
    @24
    @1
    @2
    @87
    c.mi
    @24
    wceq
    @89
    @93
    @96
    @99
    @102
    @105
    @107
    @109
    @87
    @24
    c.mi
    @84
    @85
    @86
    simp2
    eqcomd
    ad8antr
    #
    oveqd
    @110
    c.mi
    @24
    @10
    @11
    @112
    oveqd
    eqeq12d
    @110
    @61
    @28
    @62
    @29
    @110
    c.mi
    @24
    @2
    @4
    @112
    oveqd
    @110
    c.mi
    @24
    @11
    @13
    @112
    oveqd
    eqeq12d
    anbi12d
    @110
    @67
    @34
    @70
    @37
    @110
    @65
    @32
    @66
    @33
    @110
    c.mi
    @24
    @1
    @5
    @112
    oveqd
    @110
    c.mi
    @24
    @10
    @14
    @112
    oveqd
    eqeq12d
    @110
    @68
    @35
    @69
    @36
    @110
    c.mi
    @24
    @2
    @5
    @112
    oveqd
    @110
    c.mi
    @24
    @11
    @14
    @112
    oveqd
    eqeq12d
    anbi12d
    3anbi123d
    3anbi3d
    rexeqbidva
    rexeqbidva
    rexeqbidva
    rexeqbidva
    rexeqbidva
    rexeqbidva
    rexeqbidva
    rexeqbidva
    sbcie3s
    adantl
    opabbidv
    brafs.g
    @82
    cvv
    wcel
    wph
    @82
    @0
    cP
    cP
    cxp
    #
    @113
    cxp
    #
    wcel
    #
    @9
    @114
    wcel
    #
    wa
    #
    ve
    vf
    copab
    #
    @114
    @114
    cxp
    @118
    cvv
    ve
    vf
    @114
    @114
    df-xp
    @114
    @114
    @113
    @113
    cP
    cP
    cP
    cG
    cbs
    cfv
    cvv
    brafs.p
    cG
    cbs
    fvex
    eqeltri
    #
    @119
    xpex
    #
    @120
    xpex
    #
    @121
    xpex
    eqeltrri
    @81
    @117
    ve
    vf
    @81
    @8
    @17
    wa
    #
    vw
    cP
    wrex
    #
    vz
    cP
    wrex
    #
    vy
    cP
    wrex
    #
    vx
    cP
    wrex
    #
    vd
    cP
    wrex
    #
    vc
    cP
    wrex
    #
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    @117
    @80
    @129
    va
    cP
    @79
    @128
    vb
    cP
    @78
    @127
    vc
    cP
    @77
    @126
    vd
    cP
    @76
    @125
    vx
    cP
    @75
    @124
    vy
    cP
    @74
    @123
    vz
    cP
    @73
    @122
    vw
    cP
    @8
    @17
    @72
    3simpa
    reximi
    reximi
    reximi
    reximi
    reximi
    reximi
    reximi
    reximi
    @128
    @117
    va
    vb
    cP
    cP
    @89
    @93
    wa
    #
    @127
    @117
    vc
    cP
    @130
    @96
    wa
    #
    @126
    @117
    vd
    cP
    @131
    @99
    wa
    #
    @125
    @117
    vx
    cP
    @132
    @102
    wa
    #
    @124
    @117
    vy
    cP
    @133
    @105
    wa
    #
    @123
    @117
    vz
    cP
    @134
    @107
    wa
    #
    @122
    @117
    vw
    cP
    @135
    @109
    wa
    #
    @122
    @117
    @136
    @8
    @115
    @17
    @116
    @136
    @8
    wa
    #
    @0
    @7
    @114
    @136
    @8
    simpr
    @137
    @3
    @113
    wcel
    #
    @6
    @113
    wcel
    #
    @7
    @114
    wcel
    @130
    @138
    @96
    @99
    @102
    @105
    @107
    @109
    @8
    @1
    @2
    cP
    cP
    opelxpi
    ad7antr
    @137
    @96
    @99
    @139
    @130
    @96
    @99
    @102
    @105
    @107
    @109
    @8
    simp-7r
    @131
    @99
    @102
    @105
    @107
    @109
    @8
    simp-6r
    @4
    @5
    cP
    cP
    opelxpi
    syl2anc
    @3
    @6
    @113
    @113
    opelxpi
    syl2anc
    eqeltrd
    @136
    @17
    wa
    #
    @9
    @16
    @114
    @136
    @17
    simpr
    @140
    @12
    @113
    wcel
    #
    @15
    @113
    wcel
    #
    @16
    @114
    wcel
    @140
    @102
    @105
    @141
    @132
    @102
    @105
    @107
    @109
    @17
    simp-5r
    @133
    @105
    @107
    @109
    @17
    simp-4r
    @10
    @11
    cP
    cP
    opelxpi
    syl2anc
    @140
    @107
    @109
    @142
    @134
    @107
    @109
    @17
    simpllr
    @135
    @109
    @17
    simplr
    @13
    @14
    cP
    cP
    opelxpi
    syl2anc
    @12
    @15
    @113
    @113
    opelxpi
    syl2anc
    eqeltrd
    anim12dan
    ex
    rexlimdva
    rexlimdva
    rexlimdva
    rexlimdva
    rexlimdva
    rexlimdva
    rexlimivv
    syl
    ssopab2i
    ssexi
    a1i
    fvmptd
end
