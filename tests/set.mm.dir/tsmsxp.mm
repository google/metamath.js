include "ctsu.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "cres.mm"
include "cgsu.mm"
include "wi.mm"
include "cxp.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "ctopn.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "c0g.mm"
include "cplusg.mm"
include "ctmd.mm"
include "ctgp.mm"
include "tgptmd.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "ctopon.mm"
include "eqid.mm"
include "tmdtopon.mm"
include "toponss.mm"
include "syl2anc.mm"
include "simp3.mm"
include "sseldd.mm"
include "cmnd.mm"
include "tmdmnd.mm"
include "mndidcl.mm"
include "wceq.mm"
include "mndrid.mm"
include "eqeltrd.mm"
include "tmdcn2.mm"
include "syl23anc.mm"
include "r19.29.mm"
include "simp31.mm"
include "cdm.mm"
include "elfpw.mm"
include "simplbi.mm"
include "ad2antrl.mm"
include "dmss.mm"
include "dmxpss.mm"
include "syl6ss.mm"
include "simprbi.mm"
include "dmfi.mm"
include "sylanbrc.mm"
include "cmap.mm"
include "cmg.mm"
include "ccmn.mm"
include "simpl11.mm"
include "simprrl.mm"
include "simpl2r.mm"
include "chash.mm"
include "cn0.mm"
include "hashcl.mm"
include "mulgnn0z.mm"
include "simpl32.mm"
include "tmdgsum2.mm"
include "crn.mm"
include "csn.mm"
include "csg.mm"
include "simp111.mm"
include "wf.mm"
include "cmpt.mm"
include "sylan.mm"
include "simp3l.mm"
include "simp3rl.mm"
include "simp2rl.mm"
include "simp2rr.mm"
include "simp2ll.mm"
include "tsmsxplem1.mm"
include "3adant3.mm"
include "3adant3r.mm"
include "simp3ll.mm"
include "simp133.mm"
include "simp3rr.mm"
include "simpld.mm"
include "wrel.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "relssdmrn.mm"
include "xpss12.mm"
include "sylan9ss.mm"
include "syl12anc.mm"
include "simprd.mm"
include "xpfi.mm"
include "anim12i.mm"
include "an4s.mm"
include "syl2anb.mm"
include "sylibr.mm"
include "simp2lr.mm"
include "sseq2.mm"
include "reseq2.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "simp3lr.mm"
include "oveq2.mm"
include "cbvralv.mm"
include "sylib.mm"
include "tsmsxplem2.mm"
include "3exp.mm"
include "exp4a.mm"
include "3imp1.mm"
include "rexlimddv.mm"
include "3expa.mm"
include "anassrs.mm"
include "expr.mm"
include "ralrimiva.mm"
include "sseq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "rexlimdvaa.mm"
include "embantd.mm"
include "3expia.mm"
include "rexlimdva.mm"
include "com23.mm"
include "impd.mm"
include "syl5.mm"
include "mpan2d.mm"
include "ralrimdva.mm"
include "anim2d.mm"
include "cvv.mm"
include "ctps.mm"
include "tgptps.mm"
include "xpexg.mm"
include "eltsms.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem tsmsxp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let vg: setvar g
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vh: setvar h
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let cJ: class J
  let cD: class D
  let cL: class L
  let cK: class K
  let cS: class S
  let cN: class N
  let cU: class U
  let c.mi: class .-
  let cT: class T
  let c.pl: class .+
  assume tsmsxp.b: |- B = ( Base ` G )
  assume tsmsxp.g: |- ( ph -> G e. CMnd )
  assume tsmsxp.2: |- ( ph -> G e. TopGrp )
  assume tsmsxp.a: |- ( ph -> A e. V )
  assume tsmsxp.c: |- ( ph -> C e. W )
  assume tsmsxp.f: |- ( ph -> F : ( A X. C ) --> B )
  assume tsmsxp.h: |- ( ph -> H : A --> B )
  assume tsmsxp.1: |- ( ( ph /\ j e. A ) -> ( H ` j ) e. ( G tsums ( k e. C |-> ( j F k ) ) ) )

  disjoint j k
  disjoint G j
  disjoint G k
  disjoint B k
  disjoint A j
  disjoint A k
  disjoint H j
  disjoint H k
  disjoint C j
  disjoint C k
  disjoint F j
  disjoint F k
  disjoint j ph
  disjoint k ph
  disjoint g k
  disjoint g w
  disjoint g y
  disjoint g z
  disjoint .0. g
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint .0. k
  disjoint w y
  disjoint w z
  disjoint .0. w
  disjoint y z
  disjoint .0. y
  disjoint .0. z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a j
  disjoint a k
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint G a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b j
  disjoint b k
  disjoint b n
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint G b
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c j
  disjoint c k
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint G c
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d j
  disjoint d k
  disjoint d n
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint G d
  disjoint f g
  disjoint f h
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint g h
  disjoint g j
  disjoint g n
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint G g
  disjoint h j
  disjoint h k
  disjoint h n
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint G h
  disjoint j n
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k n
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint G n
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint G t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint w x
  disjoint G w
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint J y
  disjoint B b
  disjoint B g
  disjoint B h
  disjoint B s
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint D f
  disjoint D g
  disjoint D j
  disjoint D k
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint L f
  disjoint L g
  disjoint L j
  disjoint L n
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint A a
  disjoint A b
  disjoint A g
  disjoint A h
  disjoint A n
  disjoint A s
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A y
  disjoint A z
  disjoint K c
  disjoint K d
  disjoint K f
  disjoint K g
  disjoint K j
  disjoint K k
  disjoint K n
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint S c
  disjoint H a
  disjoint H b
  disjoint H d
  disjoint H f
  disjoint H g
  disjoint H h
  disjoint H n
  disjoint H s
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint N c
  disjoint N d
  disjoint N g
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint U c
  disjoint U d
  disjoint .- d
  disjoint .- f
  disjoint .- g
  disjoint .- j
  disjoint .- n
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint C b
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C n
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint C z
  disjoint T c
  disjoint T d
  disjoint T g
  disjoint .+ c
  disjoint .+ d
  disjoint .+ g
  disjoint .+ y
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F n
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint n ph
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint ph x
  assert |- ( ph -> ( G tsums F ) C_ ( G tsums H ) )

  proof
    wph
    vx
    cG
    cF
    ctsu
    co
    #
    cG
    cH
    ctsu
    co
    #
    wph
    vx
    cv
    #
    cB
    wcel
    #
    @2
    vv
    cv
    #
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    wss
    #
    cG
    cF
    @7
    cres
    #
    cgsu
    co
    #
    @4
    wcel
    #
    wi
    #
    vz
    cA
    cC
    cxp
    #
    cpw
    cfn
    cin
    #
    wral
    #
    vy
    @14
    wrex
    #
    wi
    #
    vv
    cG
    ctopn
    cfv
    #
    wral
    #
    wa
    @3
    @2
    vu
    cv
    #
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    wss
    #
    cG
    cH
    @23
    cres
    cgsu
    co
    @20
    wcel
    #
    wi
    #
    vb
    cA
    cpw
    cfn
    cin
    #
    wral
    #
    va
    @27
    wrex
    #
    wi
    #
    vu
    @18
    wral
    #
    wa
    @2
    @0
    wcel
    @2
    @1
    wcel
    wph
    @19
    @31
    @3
    wph
    @19
    @30
    vu
    @18
    wph
    @20
    @18
    wcel
    #
    wa
    @21
    @19
    @29
    wph
    @32
    @21
    @19
    @29
    wi
    wph
    @32
    @21
    w3a
    #
    @19
    @5
    cG
    c0g
    cfv
    #
    vt
    cv
    #
    wcel
    #
    vc
    cv
    vd
    cv
    cG
    cplusg
    cfv
    #
    co
    @20
    wcel
    vd
    @35
    wral
    vc
    @4
    wral
    #
    w3a
    #
    vt
    @18
    wrex
    #
    vv
    @18
    wrex
    #
    @29
    @33
    cG
    ctmd
    wcel
    #
    @32
    @3
    @34
    cB
    wcel
    #
    @2
    @34
    @37
    co
    #
    @20
    wcel
    @41
    wph
    @32
    @42
    @21
    wph
    cG
    ctgp
    wcel
    #
    @42
    tsmsxp.2
    cG
    tgptmd
    syl
    #
    3ad2ant1
    #
    wph
    @32
    @21
    simp2
    #
    @33
    @20
    cB
    @2
    @33
    @18
    cB
    ctopon
    cfv
    wcel
    #
    @32
    @20
    cB
    wss
    @33
    @42
    @49
    @47
    cG
    @18
    cB
    @18
    eqid
    #
    tsmsxp.b
    tmdtopon
    syl
    @48
    @20
    @18
    cB
    toponss
    syl2anc
    wph
    @32
    @21
    simp3
    #
    sseldd
    #
    @33
    cG
    cmnd
    wcel
    #
    @43
    @33
    @42
    @53
    @47
    cG
    tmdmnd
    #
    syl
    #
    cB
    cG
    @34
    tsmsxp.b
    @34
    eqid
    #
    mndidcl
    #
    syl
    @33
    @44
    @2
    @20
    @33
    @53
    @3
    @44
    @2
    wceq
    @55
    @52
    cB
    @37
    cG
    @2
    @34
    tsmsxp.b
    @37
    eqid
    #
    @56
    mndrid
    syl2anc
    @51
    eqeltrd
    vc
    vd
    vt
    vv
    cB
    @37
    @20
    cG
    @18
    @2
    @34
    tsmsxp.b
    @50
    @58
    tmdcn2
    syl23anc
    @19
    @41
    wa
    @17
    @40
    wa
    #
    vv
    @18
    wrex
    @33
    @29
    @17
    @40
    vv
    @18
    r19.29
    @33
    @59
    @29
    vv
    @18
    @33
    @4
    @18
    wcel
    #
    wa
    #
    @17
    @40
    @29
    @61
    @40
    @17
    @29
    @61
    @39
    @17
    @29
    wi
    #
    vt
    @18
    @33
    @60
    @35
    @18
    wcel
    #
    @39
    @62
    wi
    @33
    @60
    @63
    wa
    #
    @39
    @62
    @33
    @64
    @39
    w3a
    #
    @5
    @16
    @29
    @33
    @64
    @5
    @36
    @38
    simp31
    @65
    @15
    @29
    vy
    @14
    @65
    @6
    @14
    wcel
    #
    @15
    wa
    #
    wa
    #
    @6
    cdm
    #
    @27
    wcel
    #
    @69
    @23
    wss
    #
    @25
    wi
    #
    vb
    @27
    wral
    #
    @29
    @68
    @69
    cA
    wss
    @69
    cfn
    wcel
    #
    @70
    @68
    @69
    @13
    cdm
    #
    cA
    @68
    @6
    @13
    wss
    #
    @69
    @75
    wss
    @66
    @76
    @65
    @15
    @66
    @76
    @6
    cfn
    wcel
    #
    @6
    @13
    elfpw
    #
    simplbi
    #
    ad2antrl
    @6
    @13
    dmss
    syl
    cA
    cC
    dmxpss
    syl6ss
    @68
    @77
    @74
    @66
    @77
    @65
    @15
    @66
    @76
    @77
    @78
    simprbi
    ad2antrl
    @6
    dmfi
    syl
    @69
    cA
    elfpw
    sylanbrc
    @68
    @72
    vb
    @27
    @68
    @23
    @27
    wcel
    #
    @71
    @25
    @65
    @67
    @80
    @71
    wa
    #
    @25
    @65
    @67
    @81
    wa
    #
    wa
    #
    @34
    vs
    cv
    #
    wcel
    #
    cG
    vg
    cv
    #
    cgsu
    co
    #
    @35
    wcel
    #
    vg
    @84
    @23
    cmap
    co
    #
    wral
    #
    wa
    #
    @25
    vs
    @18
    @83
    vs
    @23
    cB
    cG
    cmg
    cfv
    #
    @35
    vg
    cG
    @18
    @34
    @50
    tsmsxp.b
    @92
    eqid
    #
    @83
    wph
    cG
    ccmn
    wcel
    #
    wph
    @32
    @21
    @64
    @39
    @82
    simpl11
    #
    tsmsxp.g
    syl
    #
    @83
    wph
    @42
    @95
    @46
    syl
    #
    @83
    @80
    @23
    cfn
    wcel
    #
    @65
    @67
    @80
    @71
    simprrl
    @80
    @23
    cA
    wss
    #
    @98
    @23
    cA
    elfpw
    #
    simprbi
    syl
    #
    @60
    @63
    @33
    @39
    @82
    simpl2r
    @83
    @53
    @43
    @83
    @42
    @53
    @97
    @54
    syl
    #
    @57
    syl
    @83
    @23
    chash
    cfv
    #
    @34
    @92
    co
    #
    @34
    @35
    @83
    @53
    @103
    cn0
    wcel
    #
    @104
    @34
    wceq
    @102
    @83
    @98
    @105
    @101
    @23
    hashcl
    syl
    cB
    @92
    cG
    @103
    @34
    tsmsxp.b
    @93
    @56
    mulgnn0z
    syl2anc
    @5
    @36
    @38
    @33
    @64
    @82
    simpl32
    eqeltrd
    tmdgsum2
    @65
    @82
    @84
    @18
    wcel
    #
    @91
    wa
    #
    @25
    @65
    @82
    @107
    w3a
    #
    @6
    crn
    #
    vn
    cv
    #
    wss
    #
    @2
    cH
    cfv
    cG
    cF
    @2
    csn
    @110
    cxp
    cres
    cgsu
    co
    cG
    csg
    cfv
    #
    co
    @84
    wcel
    vx
    @23
    wral
    #
    wa
    #
    @25
    vn
    cC
    cpw
    cfn
    cin
    #
    @108
    vx
    cA
    cB
    cC
    @6
    @37
    vj
    vk
    vn
    cF
    cG
    cH
    @18
    @23
    @84
    @112
    cV
    cW
    @34
    tsmsxp.b
    @108
    wph
    @94
    wph
    @32
    @21
    @64
    @39
    @82
    @107
    simp111
    #
    tsmsxp.g
    syl
    @108
    wph
    @45
    @116
    tsmsxp.2
    syl
    #
    @108
    wph
    cA
    cV
    wcel
    #
    @116
    tsmsxp.a
    syl
    #
    @108
    wph
    cC
    cW
    wcel
    #
    @116
    tsmsxp.c
    syl
    #
    @108
    wph
    @13
    cB
    cF
    wf
    #
    @116
    tsmsxp.f
    syl
    #
    @108
    wph
    cA
    cB
    cH
    wf
    #
    @116
    tsmsxp.h
    syl
    #
    @108
    wph
    vj
    cv
    #
    cA
    wcel
    #
    @126
    cH
    cfv
    cG
    vk
    cC
    @126
    vk
    cv
    cF
    co
    cmpt
    ctsu
    co
    wcel
    #
    @116
    tsmsxp.1
    sylan
    @50
    @56
    @58
    @112
    eqid
    #
    @65
    @82
    @106
    @91
    simp3l
    @85
    @90
    @106
    @65
    @82
    simp3rl
    #
    @80
    @71
    @67
    @65
    @107
    simp2rl
    @80
    @71
    @67
    @65
    @107
    simp2rr
    @66
    @15
    @81
    @65
    @107
    simp2ll
    tsmsxplem1
    @65
    @82
    @107
    @110
    @115
    wcel
    #
    @114
    wa
    #
    @25
    @65
    @82
    @107
    @132
    @25
    @65
    @82
    @107
    @132
    wa
    #
    @25
    @65
    @82
    @133
    w3a
    #
    vx
    cA
    cB
    cC
    @6
    @37
    @4
    @35
    @20
    vh
    vj
    vk
    cF
    cG
    cH
    @18
    @23
    @84
    @112
    @110
    cV
    cW
    @34
    vc
    vd
    tsmsxp.b
    @65
    @82
    @94
    @133
    @96
    3adant3
    @65
    @82
    @107
    @45
    @132
    @117
    3adant3r
    @65
    @82
    @107
    @118
    @132
    @119
    3adant3r
    @65
    @82
    @107
    @120
    @132
    @121
    3adant3r
    @65
    @82
    @107
    @122
    @132
    @123
    3adant3r
    @65
    @82
    @107
    @124
    @132
    @125
    3adant3r
    @134
    wph
    @127
    @128
    @65
    @82
    wph
    @133
    @95
    3adant3
    tsmsxp.1
    sylan
    @50
    @56
    @58
    @129
    @106
    @91
    @132
    @65
    @82
    simp3ll
    @65
    @82
    @107
    @85
    @132
    @130
    3adant3r
    @80
    @71
    @67
    @65
    @133
    simp2rl
    #
    @5
    @36
    @38
    @33
    @64
    @82
    @133
    simp133
    @131
    @114
    @107
    @65
    @82
    simp3rl
    #
    @134
    @66
    @71
    @111
    @6
    @23
    @110
    cxp
    #
    wss
    #
    @66
    @15
    @81
    @65
    @133
    simp2ll
    @80
    @71
    @67
    @65
    @133
    simp2rr
    @134
    @111
    @113
    @131
    @114
    @107
    @65
    @82
    simp3rr
    #
    simpld
    @66
    @71
    @111
    wa
    @6
    @69
    @109
    cxp
    #
    @137
    @66
    @6
    wrel
    #
    @6
    @140
    wss
    @66
    @76
    @13
    wrel
    @141
    @79
    cA
    cC
    relxp
    @6
    @13
    relss
    mpisyl
    @6
    relssdmrn
    syl
    @69
    @23
    @109
    @110
    xpss12
    sylan9ss
    syl12anc
    #
    @134
    @111
    @113
    @139
    simprd
    @134
    @137
    @14
    wcel
    #
    @15
    @138
    cG
    cF
    @137
    cres
    #
    cgsu
    co
    #
    @4
    wcel
    #
    @134
    @80
    @131
    @143
    @135
    @136
    @80
    @131
    wa
    @137
    @13
    wss
    #
    @137
    cfn
    wcel
    #
    wa
    #
    @143
    @80
    @99
    @98
    wa
    @110
    cC
    wss
    #
    @110
    cfn
    wcel
    #
    wa
    @149
    @131
    @100
    @110
    cC
    elfpw
    @99
    @150
    @98
    @151
    @149
    @99
    @150
    wa
    @147
    @98
    @151
    wa
    @148
    @23
    cA
    @110
    cC
    xpss12
    @23
    @110
    xpfi
    anim12i
    an4s
    syl2anb
    @137
    @13
    elfpw
    sylibr
    syl2anc
    @66
    @15
    @81
    @65
    @133
    simp2lr
    @142
    @12
    @138
    @146
    wi
    vz
    @137
    @14
    @7
    @137
    wceq
    #
    @8
    @138
    @11
    @146
    @7
    @137
    @6
    sseq2
    @152
    @10
    @145
    @4
    @152
    @9
    @144
    cG
    cgsu
    @7
    @137
    cF
    reseq2
    oveq2d
    eleq1d
    imbi12d
    rspcv
    syl3c
    @134
    @90
    cG
    vh
    cv
    #
    cgsu
    co
    #
    @35
    wcel
    #
    vh
    @89
    wral
    @134
    @85
    @90
    @106
    @91
    @132
    @65
    @82
    simp3lr
    simprd
    @88
    @155
    vg
    vh
    @89
    @86
    @153
    wceq
    @87
    @154
    @35
    @86
    @153
    cG
    cgsu
    oveq2
    eleq1d
    cbvralv
    sylib
    tsmsxplem2
    3exp
    exp4a
    3imp1
    rexlimddv
    3expa
    rexlimddv
    anassrs
    expr
    ralrimiva
    @28
    @73
    va
    @69
    @27
    @22
    @69
    wceq
    #
    @26
    @72
    vb
    @27
    @156
    @24
    @71
    @25
    @22
    @69
    @23
    sseq1
    imbi1d
    ralbidv
    rspcev
    syl2anc
    rexlimdvaa
    embantd
    3expia
    anassrs
    rexlimdva
    com23
    impd
    rexlimdva
    syl5
    mpan2d
    3expia
    com23
    ralrimdva
    anim2d
    wph
    vz
    vy
    vv
    @13
    cB
    @2
    @14
    cF
    cG
    @18
    cvv
    tsmsxp.b
    @50
    @14
    eqid
    tsmsxp.g
    wph
    @45
    cG
    ctps
    wcel
    tsmsxp.2
    cG
    tgptps
    syl
    #
    wph
    @118
    @120
    @13
    cvv
    wcel
    tsmsxp.a
    tsmsxp.c
    cA
    cC
    cV
    cW
    xpexg
    syl2anc
    tsmsxp.f
    eltsms
    wph
    vb
    va
    vu
    cA
    cB
    @2
    @27
    cH
    cG
    @18
    cV
    tsmsxp.b
    @50
    @27
    eqid
    tsmsxp.g
    @157
    tsmsxp.a
    tsmsxp.h
    eltsms
    3imtr4d
    ssrdv
end
