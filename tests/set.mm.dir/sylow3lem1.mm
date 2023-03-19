include "cgrp.mm"
include "wcel.mm"
include "cslw.mm"
include "co.mm"
include "cvv.mm"
include "wa.mm"
include "cxp.mm"
include "wf.mm"
include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wral.mm"
include "cga.mm"
include "ovex.mm"
include "jctir.mm"
include "cmpt.mm"
include "crn.mm"
include "csubg.mm"
include "chash.mm"
include "cpc.mm"
include "cexp.mm"
include "cfn.mm"
include "cprime.mm"
include "wb.mm"
include "fislw.mm"
include "syl3anc.mm"
include "biimpa.mm"
include "adantrl.mm"
include "simpld.mm"
include "simprl.mm"
include "eqid.mm"
include "conjsubg.mm"
include "syl2anc.mm"
include "cen.mm"
include "wbr.mm"
include "conjsubgen.mm"
include "wss.mm"
include "adantr.mm"
include "subgss.mm"
include "syl.mm"
include "ssfi.mm"
include "hashen.mm"
include "mpbird.mm"
include "simprd.mm"
include "eqtr3d.mm"
include "mpbir2and.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "grpidcl.mm"
include "simpr.mm"
include "weq.mm"
include "simpl.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "vex.mm"
include "mptex.mm"
include "rnex.mm"
include "ovmpt2a.mm"
include "cid.mm"
include "cres.mm"
include "ad2antrr.mm"
include "slwsubg.mm"
include "adantl.mm"
include "sselda.mm"
include "grplid.mm"
include "grpsubid1.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "mptresid.mm"
include "syl6eq.mm"
include "rnresi.mm"
include "wrex.mm"
include "cab.mm"
include "oveq2.mm"
include "abrexco.mm"
include "simprr.mm"
include "simplr.mm"
include "rnmpt.mm"
include "rexeqdv.mm"
include "abbidv.mm"
include "grpcl.mm"
include "adantlr.mm"
include "grpsubsub4.mm"
include "syl13anc.mm"
include "grpass.mm"
include "grpaddsubass.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "3eqtr4a.mm"
include "3eqtr4g.mm"
include "fovrnd.mm"
include "cbvmptv.mm"
include "3eqtr4rd.mm"
include "jca.mm"
include "ralrimiva.mm"
include "isga.mm"
include "sylanbrc.mm"

theorem sylow3lem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let cH: class H
  let cK: class K
  let vk: setvar k
  let cN: class N
  assume sylow3.x: |- X = ( Base ` G )
  assume sylow3.g: |- ( ph -> G e. Grp )
  assume sylow3.xf: |- ( ph -> X e. Fin )
  assume sylow3.p: |- ( ph -> P e. Prime )
  assume sylow3lem1.a: |- .+ = ( +g ` G )
  assume sylow3lem1.d: |- .- = ( -g ` G )
  assume sylow3lem1.m: |- .(+) = ( x e. X , y e. ( P pSyl G ) |-> ran ( z e. y |-> ( ( x .+ z ) .- x ) ) )

  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint .- a
  disjoint b c
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint .- b
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .- c
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .- u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint .- v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .- w
  disjoint a g
  disjoint a h
  disjoint a s
  disjoint .(+) a
  disjoint b g
  disjoint b h
  disjoint b s
  disjoint .(+) b
  disjoint c g
  disjoint c h
  disjoint c s
  disjoint .(+) c
  disjoint g h
  disjoint g s
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .(+) g
  disjoint h s
  disjoint h u
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint .(+) h
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint .(+) s
  disjoint .(+) u
  disjoint .(+) w
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint g v
  disjoint K g
  disjoint h v
  disjoint K h
  disjoint s v
  disjoint K s
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint g k
  disjoint N g
  disjoint k u
  disjoint k w
  disjoint k z
  disjoint N k
  disjoint N u
  disjoint N w
  disjoint N z
  disjoint a k
  disjoint X a
  disjoint b k
  disjoint X b
  disjoint c k
  disjoint X c
  disjoint X g
  disjoint h k
  disjoint X h
  disjoint k x
  disjoint k y
  disjoint X k
  disjoint X u
  disjoint X w
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G g
  disjoint G h
  disjoint k s
  disjoint G k
  disjoint G s
  disjoint G u
  disjoint G w
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint g ph
  disjoint h ph
  disjoint k ph
  disjoint ph s
  disjoint ph u
  disjoint ph w
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+ g
  disjoint .+ u
  disjoint .+ v
  disjoint .+ w
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P g
  disjoint P h
  disjoint P k
  disjoint P s
  disjoint P u
  disjoint P w
  assert |- ( ph -> .(+) e. ( G GrpAct ( P pSyl G ) ) )

  proof
    wph
    cG
    cgrp
    wcel
    #
    cP
    cG
    cslw
    co
    #
    cvv
    wcel
    #
    wa
    cX
    @1
    cxp
    @1
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
    @5
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
    @5
    c.po
    co
    #
    @8
    @9
    @5
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
    @1
    wral
    #
    wa
    c.po
    cG
    @1
    cga
    co
    wcel
    wph
    @0
    @2
    sylow3.g
    cP
    cG
    cslw
    ovex
    jctir
    wph
    @3
    @17
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
    @19
    c.mi
    co
    #
    cmpt
    #
    crn
    #
    @1
    wcel
    #
    vy
    @1
    wral
    vx
    cX
    wral
    @3
    wph
    @25
    vx
    vy
    cX
    @1
    wph
    @19
    cX
    wcel
    #
    @18
    @1
    wcel
    #
    wa
    #
    wa
    #
    @25
    @24
    cG
    csubg
    cfv
    #
    wcel
    #
    @24
    chash
    cfv
    #
    cP
    cP
    cX
    chash
    cfv
    cpc
    co
    cexp
    co
    #
    wceq
    #
    @29
    @18
    @30
    wcel
    #
    @26
    @31
    @29
    @35
    @18
    chash
    cfv
    #
    @33
    wceq
    #
    wph
    @27
    @35
    @37
    wa
    #
    @26
    wph
    @27
    @38
    wph
    @0
    cX
    cfn
    wcel
    #
    cP
    cprime
    wcel
    #
    @27
    @38
    wb
    sylow3.g
    sylow3.xf
    sylow3.p
    cP
    cG
    @18
    cX
    sylow3.x
    fislw
    syl3anc
    biimpa
    adantrl
    #
    simpld
    #
    wph
    @26
    @27
    simprl
    #
    vz
    @19
    c.pl
    @18
    @23
    cG
    c.mi
    cX
    sylow3.x
    sylow3lem1.a
    sylow3lem1.d
    @23
    eqid
    #
    conjsubg
    syl2anc
    #
    @29
    @36
    @32
    @33
    @29
    @36
    @32
    wceq
    #
    @18
    @24
    cen
    wbr
    #
    @29
    @35
    @26
    @47
    @42
    @43
    vz
    @19
    c.pl
    @18
    @23
    cG
    c.mi
    cX
    sylow3.x
    sylow3lem1.a
    sylow3lem1.d
    @44
    conjsubgen
    syl2anc
    @29
    @18
    cfn
    wcel
    #
    @24
    cfn
    wcel
    #
    @46
    @47
    wb
    @29
    @39
    @18
    cX
    wss
    #
    @48
    wph
    @39
    @28
    sylow3.xf
    adantr
    #
    @29
    @35
    @50
    @42
    cX
    @18
    cG
    sylow3.x
    subgss
    syl
    cX
    @18
    ssfi
    syl2anc
    @29
    @39
    @24
    cX
    wss
    #
    @49
    @51
    @29
    @31
    @52
    @45
    cX
    @24
    cG
    sylow3.x
    subgss
    syl
    cX
    @24
    ssfi
    syl2anc
    @18
    @24
    hashen
    syl2anc
    mpbird
    @29
    @35
    @37
    @41
    simprd
    eqtr3d
    wph
    @25
    @31
    @34
    wa
    wb
    #
    @28
    wph
    @0
    @39
    @40
    @53
    sylow3.g
    sylow3.xf
    sylow3.p
    cP
    cG
    @24
    cX
    sylow3.x
    fislw
    syl3anc
    adantr
    mpbir2and
    ralrimivva
    vx
    vy
    cX
    @1
    @24
    @1
    c.po
    sylow3lem1.m
    fmpt2
    sylib
    #
    wph
    @16
    va
    @1
    wph
    @5
    @1
    wcel
    #
    wa
    #
    @7
    @15
    @56
    @6
    vz
    @5
    @4
    @20
    c.pl
    co
    #
    @4
    c.mi
    co
    #
    cmpt
    #
    crn
    #
    @5
    @56
    @4
    cX
    wcel
    #
    @55
    @6
    @60
    wceq
    @56
    @0
    @61
    wph
    @0
    @55
    sylow3.g
    adantr
    #
    cX
    cG
    @4
    sylow3.x
    @4
    eqid
    #
    grpidcl
    syl
    wph
    @55
    simpr
    vx
    vy
    @4
    @5
    cX
    @1
    @24
    @60
    c.po
    @19
    @4
    wceq
    #
    vy
    va
    weq
    #
    wa
    #
    @23
    @59
    @66
    vz
    @18
    @22
    @5
    @58
    @64
    @65
    simpr
    @66
    @21
    @57
    @19
    @4
    c.mi
    @66
    @19
    @4
    @20
    c.pl
    @64
    @65
    simpl
    #
    oveq1d
    @67
    oveq12d
    mpteq12dv
    rneqd
    sylow3lem1.m
    @59
    vz
    @5
    @58
    va
    vex
    #
    mptex
    rnex
    ovmpt2a
    syl2anc
    @56
    @60
    cid
    @5
    cres
    #
    crn
    @5
    @56
    @59
    @69
    @56
    @59
    vz
    @5
    @20
    cmpt
    @69
    @56
    vz
    @5
    @58
    @20
    @56
    @20
    @5
    wcel
    #
    wa
    #
    @58
    @20
    @4
    c.mi
    co
    #
    @20
    @71
    @57
    @20
    @4
    c.mi
    @71
    @0
    @20
    cX
    wcel
    #
    @57
    @20
    wceq
    wph
    @0
    @55
    @70
    sylow3.g
    ad2antrr
    #
    @56
    @5
    cX
    @20
    @56
    @5
    @30
    wcel
    #
    @5
    cX
    wss
    @55
    @75
    wph
    cP
    cG
    @5
    slwsubg
    adantl
    cX
    @5
    cG
    sylow3.x
    subgss
    syl
    sselda
    #
    cX
    c.pl
    cG
    @20
    @4
    sylow3.x
    sylow3lem1.a
    @63
    grplid
    syl2anc
    oveq1d
    @71
    @0
    @73
    @72
    @20
    wceq
    @74
    @76
    cX
    cG
    c.mi
    @20
    @4
    sylow3.x
    @63
    sylow3lem1.d
    grpsubid1
    syl2anc
    eqtrd
    mpteq2dva
    vz
    @5
    mptresid
    syl6eq
    rneqd
    @5
    rnresi
    syl6eq
    eqtrd
    @56
    @14
    vb
    vc
    cX
    cX
    @56
    @8
    cX
    wcel
    #
    @9
    cX
    wcel
    #
    wa
    #
    wa
    #
    vw
    @12
    @8
    vw
    cv
    #
    c.pl
    co
    #
    @8
    c.mi
    co
    #
    cmpt
    #
    crn
    #
    vz
    @5
    @10
    @20
    c.pl
    co
    #
    @10
    c.mi
    co
    #
    cmpt
    #
    crn
    #
    @13
    @11
    @80
    vu
    cv
    #
    @83
    wceq
    #
    vw
    @12
    wrex
    #
    vu
    cab
    #
    @90
    @87
    wceq
    #
    vz
    @5
    wrex
    #
    vu
    cab
    #
    @85
    @89
    @80
    @91
    vw
    vv
    cv
    @9
    @20
    c.pl
    co
    #
    @9
    c.mi
    co
    #
    wceq
    vz
    @5
    wrex
    vv
    cab
    #
    wrex
    #
    vu
    cab
    @90
    @8
    @98
    c.pl
    co
    #
    @8
    c.mi
    co
    #
    wceq
    #
    vz
    @5
    wrex
    #
    vu
    cab
    @93
    @96
    vu
    vw
    vv
    vz
    @5
    @98
    @83
    @102
    @97
    @9
    c.mi
    ovex
    @81
    @98
    wceq
    @82
    @101
    @8
    c.mi
    @81
    @98
    @8
    c.pl
    oveq2
    oveq1d
    abrexco
    @80
    @92
    @100
    vu
    @80
    @91
    vw
    @12
    @99
    @80
    @12
    vz
    @5
    @98
    cmpt
    #
    crn
    #
    @99
    @80
    @78
    @55
    @12
    @106
    wceq
    @56
    @77
    @78
    simprr
    #
    wph
    @55
    @79
    simplr
    #
    vx
    vy
    @9
    @5
    cX
    @1
    @24
    @106
    c.po
    vx
    vc
    weq
    #
    @65
    wa
    #
    @23
    @105
    @110
    vz
    @18
    @22
    @5
    @98
    @109
    @65
    simpr
    @110
    @21
    @97
    @19
    @9
    c.mi
    @110
    @19
    @9
    @20
    c.pl
    @109
    @65
    simpl
    #
    oveq1d
    @111
    oveq12d
    mpteq12dv
    rneqd
    sylow3lem1.m
    @105
    vz
    @5
    @98
    @68
    mptex
    rnex
    ovmpt2a
    syl2anc
    vz
    vv
    @5
    @98
    @105
    @105
    eqid
    rnmpt
    syl6eq
    rexeqdv
    abbidv
    @80
    @95
    @104
    vu
    @80
    @94
    @103
    vz
    @5
    @80
    @70
    wa
    #
    @87
    @102
    @90
    @112
    @86
    @9
    c.mi
    co
    #
    @8
    c.mi
    co
    #
    @87
    @102
    @112
    @0
    @86
    cX
    wcel
    #
    @78
    @77
    @114
    @87
    wceq
    @80
    @0
    @70
    @56
    @0
    @79
    @62
    adantr
    #
    adantr
    #
    @112
    @0
    @10
    cX
    wcel
    #
    @73
    @115
    @117
    @80
    @118
    @70
    @80
    @0
    @77
    @78
    @118
    @116
    @56
    @77
    @78
    simprl
    #
    @107
    cX
    c.pl
    cG
    @8
    @9
    sylow3.x
    sylow3lem1.a
    grpcl
    syl3anc
    #
    adantr
    @56
    @70
    @73
    @79
    @76
    adantlr
    #
    cX
    c.pl
    cG
    @10
    @20
    sylow3.x
    sylow3lem1.a
    grpcl
    syl3anc
    @80
    @78
    @70
    @107
    adantr
    #
    @80
    @77
    @70
    @119
    adantr
    #
    cX
    c.pl
    cG
    c.mi
    @86
    @9
    @8
    sylow3.x
    sylow3lem1.a
    sylow3lem1.d
    grpsubsub4
    syl13anc
    @112
    @113
    @101
    @8
    c.mi
    @112
    @113
    @8
    @97
    c.pl
    co
    #
    @9
    c.mi
    co
    #
    @101
    @112
    @86
    @124
    @9
    c.mi
    @112
    @0
    @77
    @78
    @73
    @86
    @124
    wceq
    @117
    @123
    @122
    @121
    cX
    c.pl
    cG
    @8
    @9
    @20
    sylow3.x
    sylow3lem1.a
    grpass
    syl13anc
    oveq1d
    @112
    @0
    @77
    @97
    cX
    wcel
    #
    @78
    @125
    @101
    wceq
    @117
    @123
    @112
    @0
    @78
    @73
    @126
    @117
    @122
    @121
    cX
    c.pl
    cG
    @9
    @20
    sylow3.x
    sylow3lem1.a
    grpcl
    syl3anc
    @122
    cX
    c.pl
    cG
    c.mi
    @8
    @97
    @9
    sylow3.x
    sylow3lem1.a
    sylow3lem1.d
    grpaddsubass
    syl13anc
    eqtrd
    oveq1d
    eqtr3d
    eqeq2d
    rexbidva
    abbidv
    3eqtr4a
    vw
    vu
    @12
    @83
    @84
    @84
    eqid
    rnmpt
    vz
    vu
    @5
    @87
    @88
    @88
    eqid
    rnmpt
    3eqtr4g
    @80
    @77
    @12
    @1
    wcel
    @13
    @85
    wceq
    @119
    @80
    @9
    @5
    @1
    cX
    @1
    c.po
    wph
    @3
    @55
    @79
    @54
    ad2antrr
    @107
    @108
    fovrnd
    vx
    vy
    @8
    @12
    cX
    @1
    @24
    @85
    c.po
    vx
    vb
    weq
    #
    @18
    @12
    wceq
    #
    wa
    #
    @23
    @84
    @129
    @23
    vz
    @12
    @8
    @20
    c.pl
    co
    #
    @8
    c.mi
    co
    #
    cmpt
    @84
    @129
    vz
    @18
    @22
    @12
    @131
    @127
    @128
    simpr
    @129
    @21
    @130
    @19
    @8
    c.mi
    @129
    @19
    @8
    @20
    c.pl
    @127
    @128
    simpl
    #
    oveq1d
    @132
    oveq12d
    mpteq12dv
    vz
    vw
    @12
    @131
    @83
    vz
    vw
    weq
    @130
    @82
    @8
    c.mi
    @20
    @81
    @8
    c.pl
    oveq2
    oveq1d
    cbvmptv
    syl6eq
    rneqd
    sylow3lem1.m
    @84
    vw
    @12
    @83
    @9
    @5
    c.po
    ovex
    mptex
    rnex
    ovmpt2a
    syl2anc
    @80
    @118
    @55
    @11
    @89
    wceq
    @120
    @108
    vx
    vy
    @10
    @5
    cX
    @1
    @24
    @89
    c.po
    @19
    @10
    wceq
    #
    @65
    wa
    #
    @23
    @88
    @134
    vz
    @18
    @22
    @5
    @87
    @133
    @65
    simpr
    @134
    @21
    @86
    @19
    @10
    c.mi
    @134
    @19
    @10
    @20
    c.pl
    @133
    @65
    simpl
    #
    oveq1d
    @135
    oveq12d
    mpteq12dv
    rneqd
    sylow3lem1.m
    @88
    vz
    @5
    @87
    @68
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
    @1
    @4
    sylow3.x
    sylow3lem1.a
    @63
    isga
    sylanbrc
end
