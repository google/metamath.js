include "cgrp.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cxp.mm"
include "wf.mm"
include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cga.mm"
include "chash.mm"
include "cexp.mm"
include "cpw.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "rabex2.mm"
include "jctir.mm"
include "cmpt.mm"
include "crn.mm"
include "wss.mm"
include "wf1.mm"
include "cres.mm"
include "wf1o.mm"
include "simprl.mm"
include "eqid.mm"
include "grplmulf1o.mm"
include "syl2an2r.mm"
include "f1of1.mm"
include "syl.mm"
include "simprr.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "sylib.mm"
include "simpld.mm"
include "elpwid.mm"
include "f1ssres.mm"
include "syl2anc.mm"
include "wb.mm"
include "resmpt.mm"
include "f1eq1.mm"
include "3syl.mm"
include "mpbid.mm"
include "f1f.mm"
include "frn.mm"
include "elpw2.mm"
include "sylibr.mm"
include "cen.mm"
include "wbr.mm"
include "f1f1orn.mm"
include "vex.mm"
include "f1oen.mm"
include "cfn.mm"
include "ssfi.mm"
include "hashen.mm"
include "mpbird.mm"
include "simprd.mm"
include "eqtr3d.mm"
include "sylanbrc.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "adantr.mm"
include "grpidcl.mm"
include "simpr.mm"
include "simpl.mm"
include "oveq1d.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "mptex.mm"
include "rnex.mm"
include "ovmpt2a.mm"
include "cid.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "sselda.mm"
include "grplid.mm"
include "mpteq2dva.mm"
include "mptresid.mm"
include "syl6eq.mm"
include "rnresi.mm"
include "eqtrd.mm"
include "wrex.mm"
include "cab.mm"
include "ovex.mm"
include "oveq2.mm"
include "abrexco.mm"
include "rnmpt.mm"
include "rexeqdv.mm"
include "abbidv.mm"
include "ad2antrr.mm"
include "adantlr.mm"
include "grpass.mm"
include "syl13anc.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "3eqtr4a.mm"
include "3eqtr4g.mm"
include "fovrnd.mm"
include "cbvmptv.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "3eqtr4rd.mm"
include "jca.mm"
include "ralrimiva.mm"
include "isga.mm"

theorem sylow1lem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cS: class S
  let cG: class G
  let cN: class N
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vg: setvar g
  let vu: setvar u
  let cB: class B
  let vh: setvar h
  let cH: class H
  let vw: setvar w
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vv: setvar v
  let c.sm: class .~
  assume sylow1.x: |- X = ( Base ` G )
  assume sylow1.g: |- ( ph -> G e. Grp )
  assume sylow1.f: |- ( ph -> X e. Fin )
  assume sylow1.p: |- ( ph -> P e. Prime )
  assume sylow1.n: |- ( ph -> N e. NN0 )
  assume sylow1.d: |- ( ph -> ( P ^ N ) || ( # ` X ) )
  assume sylow1lem.a: |- .+ = ( +g ` G )
  assume sylow1lem.s: |- S = { s e. ~P X | ( # ` s ) = ( P ^ N ) }
  assume sylow1lem.m: |- .(+) = ( x e. X , y e. S |-> ran ( z e. y |-> ( x .+ z ) ) )

  disjoint s x
  disjoint s y
  disjoint s z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint N s
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint .+ s
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint G s
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint P s
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint a b
  disjoint a c
  disjoint a g
  disjoint a s
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint B a
  disjoint b c
  disjoint b g
  disjoint b s
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint c g
  disjoint c s
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint g s
  disjoint g u
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint s u
  disjoint B s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a h
  disjoint H a
  disjoint b h
  disjoint H b
  disjoint c h
  disjoint H c
  disjoint g h
  disjoint H g
  disjoint h x
  disjoint h y
  disjoint H h
  disjoint H x
  disjoint H y
  disjoint a w
  disjoint S a
  disjoint b w
  disjoint S b
  disjoint c w
  disjoint S c
  disjoint g w
  disjoint S g
  disjoint u w
  disjoint S u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint S w
  disjoint a k
  disjoint a n
  disjoint a t
  disjoint a v
  disjoint N a
  disjoint b k
  disjoint b n
  disjoint b t
  disjoint b v
  disjoint N b
  disjoint g k
  disjoint g n
  disjoint g t
  disjoint g v
  disjoint N g
  disjoint h k
  disjoint h n
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h z
  disjoint N h
  disjoint k n
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint N n
  disjoint s t
  disjoint s v
  disjoint s w
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint N t
  disjoint u v
  disjoint N u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint N v
  disjoint N w
  disjoint X a
  disjoint X b
  disjoint c k
  disjoint c n
  disjoint c t
  disjoint c v
  disjoint X c
  disjoint X g
  disjoint X h
  disjoint X k
  disjoint X n
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint .+ b
  disjoint .+ c
  disjoint .+ u
  disjoint .+ v
  disjoint .+ w
  disjoint .~ a
  disjoint .~ w
  disjoint .~ z
  disjoint .(+) a
  disjoint .(+) b
  disjoint .(+) c
  disjoint .(+) g
  disjoint .(+) u
  disjoint .(+) w
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G g
  disjoint G h
  disjoint G k
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint P a
  disjoint P b
  disjoint P g
  disjoint P h
  disjoint P k
  disjoint P n
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  assert |- ( ph -> .(+) e. ( G GrpAct S ) )

  proof
    wph
    cG
    cgrp
    wcel
    #
    cS
    cvv
    wcel
    #
    wa
    cX
    cS
    cxp
    cS
    c.po
    wf
    #
    cG
    c0g
    cfv
    #
    va
    cv
    #
    c.po
    co
    #
    @4
    wceq
    #
    vb
    cv
    #
    vc
    cv
    #
    c.pl
    co
    #
    @4
    c.po
    co
    #
    @7
    @8
    @4
    c.po
    co
    #
    c.po
    co
    #
    wceq
    #
    vc
    cX
    wral
    vb
    cX
    wral
    #
    wa
    #
    va
    cS
    wral
    #
    wa
    c.po
    cG
    cS
    cga
    co
    wcel
    wph
    @0
    @1
    sylow1.g
    vs
    cv
    #
    chash
    cfv
    #
    cP
    cN
    cexp
    co
    #
    wceq
    #
    vs
    cX
    cpw
    #
    cS
    sylow1lem.s
    cX
    cX
    cG
    cbs
    cfv
    cvv
    sylow1.x
    cG
    cbs
    fvex
    eqeltri
    #
    pwex
    rabex2
    jctir
    wph
    @2
    @16
    wph
    vz
    vy
    cv
    #
    vx
    cv
    #
    vz
    cv
    #
    c.pl
    co
    #
    cmpt
    #
    crn
    #
    cS
    wcel
    #
    vy
    cS
    wral
    vx
    cX
    wral
    @2
    wph
    @29
    vx
    vy
    cX
    cS
    wph
    @24
    cX
    wcel
    #
    @23
    cS
    wcel
    #
    wa
    #
    wa
    #
    @28
    @21
    wcel
    #
    @28
    chash
    cfv
    #
    @19
    wceq
    #
    @29
    @33
    @28
    cX
    wss
    #
    @34
    @33
    @23
    cX
    @27
    wf1
    #
    @23
    cX
    @27
    wf
    @37
    @33
    @23
    cX
    vz
    cX
    @26
    cmpt
    #
    @23
    cres
    #
    wf1
    #
    @38
    @33
    cX
    cX
    @39
    wf1
    #
    @23
    cX
    wss
    #
    @41
    @33
    cX
    cX
    @39
    wf1o
    #
    @42
    wph
    @0
    @32
    @30
    @44
    sylow1.g
    wph
    @30
    @31
    simprl
    vz
    cX
    c.pl
    @39
    cG
    @24
    sylow1.x
    sylow1lem.a
    @39
    eqid
    grplmulf1o
    syl2an2r
    cX
    cX
    @39
    f1of1
    syl
    @33
    @23
    cX
    @33
    @23
    @21
    wcel
    #
    @23
    chash
    cfv
    #
    @19
    wceq
    #
    @33
    @31
    @45
    @47
    wa
    wph
    @30
    @31
    simprr
    @20
    @47
    vs
    @23
    @21
    cS
    vs
    vy
    weq
    @18
    @46
    @19
    @17
    @23
    chash
    fveq2
    eqeq1d
    sylow1lem.s
    elrab2
    sylib
    #
    simpld
    elpwid
    #
    cX
    cX
    @23
    @39
    f1ssres
    syl2anc
    @33
    @43
    @40
    @27
    wceq
    @41
    @38
    wb
    @49
    vz
    cX
    @23
    @26
    resmpt
    @23
    cX
    @40
    @27
    f1eq1
    3syl
    mpbid
    #
    @23
    cX
    @27
    f1f
    @23
    cX
    @27
    frn
    3syl
    #
    @28
    cX
    @22
    elpw2
    sylibr
    @33
    @46
    @35
    @19
    @33
    @46
    @35
    wceq
    #
    @23
    @28
    cen
    wbr
    #
    @33
    @38
    @23
    @28
    @27
    wf1o
    @53
    @50
    @23
    cX
    @27
    f1f1orn
    @23
    @28
    @27
    vy
    vex
    f1oen
    3syl
    @33
    @23
    cfn
    wcel
    #
    @28
    cfn
    wcel
    #
    @52
    @53
    wb
    wph
    cX
    cfn
    wcel
    #
    @32
    @43
    @54
    sylow1.f
    @49
    cX
    @23
    ssfi
    syl2an2r
    wph
    @56
    @32
    @37
    @55
    sylow1.f
    @51
    cX
    @28
    ssfi
    syl2an2r
    @23
    @28
    hashen
    syl2anc
    mpbird
    @33
    @45
    @47
    @48
    simprd
    eqtr3d
    @20
    @36
    vs
    @28
    @21
    cS
    @17
    @28
    wceq
    @18
    @35
    @19
    @17
    @28
    chash
    fveq2
    eqeq1d
    sylow1lem.s
    elrab2
    sylanbrc
    ralrimivva
    vx
    vy
    cX
    cS
    @28
    cS
    c.po
    sylow1lem.m
    fmpt2
    sylib
    #
    wph
    @15
    va
    cS
    wph
    @4
    cS
    wcel
    #
    wa
    #
    @6
    @14
    @59
    @5
    vz
    @4
    @3
    @25
    c.pl
    co
    #
    cmpt
    #
    crn
    #
    @4
    @59
    @3
    cX
    wcel
    #
    @58
    @5
    @62
    wceq
    @59
    @0
    @63
    wph
    @0
    @58
    sylow1.g
    adantr
    #
    cX
    cG
    @3
    sylow1.x
    @3
    eqid
    #
    grpidcl
    syl
    wph
    @58
    simpr
    #
    vx
    vy
    @3
    @4
    cX
    cS
    @28
    @62
    c.po
    @24
    @3
    wceq
    #
    vy
    va
    weq
    #
    wa
    #
    @27
    @61
    @69
    vz
    @23
    @26
    @4
    @60
    @67
    @68
    simpr
    @69
    @24
    @3
    @25
    c.pl
    @67
    @68
    simpl
    oveq1d
    mpteq12dv
    rneqd
    sylow1lem.m
    @61
    vz
    @4
    @60
    va
    vex
    #
    mptex
    rnex
    ovmpt2a
    syl2anc
    @59
    @62
    cid
    @4
    cres
    #
    crn
    @4
    @59
    @61
    @71
    @59
    @61
    vz
    @4
    @25
    cmpt
    @71
    @59
    vz
    @4
    @60
    @25
    @59
    @0
    @25
    @4
    wcel
    #
    @25
    cX
    wcel
    #
    @60
    @25
    wceq
    @64
    @59
    @4
    cX
    @25
    @59
    @4
    cX
    @59
    cS
    @21
    @4
    cS
    @20
    vs
    @21
    crab
    @21
    sylow1lem.s
    @20
    vs
    @21
    ssrab2
    eqsstri
    @66
    sseldi
    elpwid
    sselda
    #
    cX
    c.pl
    cG
    @25
    @3
    sylow1.x
    sylow1lem.a
    @65
    grplid
    syl2an2r
    mpteq2dva
    vz
    @4
    mptresid
    syl6eq
    rneqd
    @4
    rnresi
    syl6eq
    eqtrd
    @59
    @13
    vb
    vc
    cX
    cX
    @59
    @7
    cX
    wcel
    #
    @8
    cX
    wcel
    #
    wa
    #
    wa
    #
    vw
    @11
    @7
    vw
    cv
    #
    c.pl
    co
    #
    cmpt
    #
    crn
    #
    vz
    @4
    @9
    @25
    c.pl
    co
    #
    cmpt
    #
    crn
    #
    @12
    @10
    @78
    vu
    cv
    #
    @80
    wceq
    #
    vw
    @11
    wrex
    #
    vu
    cab
    #
    @86
    @83
    wceq
    #
    vz
    @4
    wrex
    #
    vu
    cab
    #
    @82
    @85
    @78
    @87
    vw
    vv
    cv
    @8
    @25
    c.pl
    co
    #
    wceq
    vz
    @4
    wrex
    vv
    cab
    #
    wrex
    #
    vu
    cab
    @86
    @7
    @93
    c.pl
    co
    #
    wceq
    #
    vz
    @4
    wrex
    #
    vu
    cab
    @89
    @92
    vu
    vw
    vv
    vz
    @4
    @93
    @80
    @96
    @8
    @25
    c.pl
    ovex
    @79
    @93
    @7
    c.pl
    oveq2
    abrexco
    @78
    @88
    @95
    vu
    @78
    @87
    vw
    @11
    @94
    @78
    @11
    vz
    @4
    @93
    cmpt
    #
    crn
    #
    @94
    @78
    @76
    @58
    @11
    @100
    wceq
    @59
    @75
    @76
    simprr
    #
    @59
    @58
    @77
    @66
    adantr
    #
    vx
    vy
    @8
    @4
    cX
    cS
    @28
    @100
    c.po
    vx
    vc
    weq
    #
    @68
    wa
    #
    @27
    @99
    @104
    vz
    @23
    @26
    @4
    @93
    @103
    @68
    simpr
    @104
    @24
    @8
    @25
    c.pl
    @103
    @68
    simpl
    oveq1d
    mpteq12dv
    rneqd
    sylow1lem.m
    @99
    vz
    @4
    @93
    @70
    mptex
    rnex
    ovmpt2a
    syl2anc
    vz
    vv
    @4
    @93
    @99
    @99
    eqid
    rnmpt
    syl6eq
    rexeqdv
    abbidv
    @78
    @91
    @98
    vu
    @78
    @90
    @97
    vz
    @4
    @78
    @72
    wa
    #
    @83
    @96
    @86
    @105
    @0
    @75
    @76
    @73
    @83
    @96
    wceq
    @59
    @0
    @77
    @72
    @64
    ad2antrr
    @78
    @75
    @72
    @59
    @75
    @76
    simprl
    #
    adantr
    @78
    @76
    @72
    @101
    adantr
    @59
    @72
    @73
    @77
    @74
    adantlr
    cX
    c.pl
    cG
    @7
    @8
    @25
    sylow1.x
    sylow1lem.a
    grpass
    syl13anc
    eqeq2d
    rexbidva
    abbidv
    3eqtr4a
    vw
    vu
    @11
    @80
    @81
    @81
    eqid
    rnmpt
    vz
    vu
    @4
    @83
    @84
    @84
    eqid
    rnmpt
    3eqtr4g
    @78
    @75
    @11
    cS
    wcel
    @12
    @82
    wceq
    @106
    @78
    @8
    @4
    cS
    cX
    cS
    c.po
    wph
    @2
    @58
    @77
    @57
    ad2antrr
    @101
    @102
    fovrnd
    vx
    vy
    @7
    @11
    cX
    cS
    @28
    @82
    c.po
    vx
    vb
    weq
    #
    @23
    @11
    wceq
    #
    wa
    #
    @27
    @81
    @109
    @27
    vz
    @11
    @7
    @25
    c.pl
    co
    #
    cmpt
    @81
    @109
    vz
    @23
    @26
    @11
    @110
    @107
    @108
    simpr
    @109
    @24
    @7
    @25
    c.pl
    @107
    @108
    simpl
    oveq1d
    mpteq12dv
    vz
    vw
    @11
    @110
    @80
    @25
    @79
    @7
    c.pl
    oveq2
    cbvmptv
    syl6eq
    rneqd
    sylow1lem.m
    @81
    vw
    @11
    @80
    @8
    @4
    c.po
    ovex
    mptex
    rnex
    ovmpt2a
    syl2anc
    @78
    @9
    cX
    wcel
    #
    @58
    @10
    @85
    wceq
    @78
    @0
    @75
    @76
    @111
    wph
    @0
    @58
    @77
    sylow1.g
    ad2antrr
    @106
    @101
    cX
    c.pl
    cG
    @7
    @8
    sylow1.x
    sylow1lem.a
    grpcl
    syl3anc
    @102
    vx
    vy
    @9
    @4
    cX
    cS
    @28
    @85
    c.po
    @24
    @9
    wceq
    #
    @68
    wa
    #
    @27
    @84
    @113
    vz
    @23
    @26
    @4
    @83
    @112
    @68
    simpr
    @113
    @24
    @9
    @25
    c.pl
    @112
    @68
    simpl
    oveq1d
    mpteq12dv
    rneqd
    sylow1lem.m
    @84
    vz
    @4
    @83
    @70
    mptex
    rnex
    ovmpt2a
    syl2anc
    3eqtr4rd
    ralrimivva
    jca
    ralrimiva
    jca
    va
    vb
    vc
    c.pl
    c.po
    cG
    cX
    cS
    @3
    sylow1.x
    sylow1lem.a
    @65
    isga
    sylanbrc
end
