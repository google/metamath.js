include "ctx.mm"
include "co.mm"
include "cxko.mm"
include "ccn.mm"
include "wcel.mm"
include "ccnv.mm"
include "chmeo.mm"
include "cv.mm"
include "cmpt.mm"
include "ctop.mm"
include "ctopon.mm"
include "cfv.mm"
include "cxp.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "topontop.mm"
include "syl.mm"
include "eqid.mm"
include "xkotopon.mm"
include "cmpt2.mm"
include "c2nd.mm"
include "c1st.mm"
include "cop.mm"
include "wceq.mm"
include "vex.mm"
include "op1std.mm"
include "op2ndd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "mpteq2dv.mm"
include "mpt2mpt.mm"
include "fveq2d.mm"
include "cuni.mm"
include "toptopon.mm"
include "sylib.mm"
include "ccmp.mm"
include "cnlly.mm"
include "txcmp.mm"
include "txnlly.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "xp1st.mm"
include "adantl.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "feqmptd.mm"
include "mpteq2dva.mm"
include "syl5eqr.mm"
include "cnmpt1st.mm"
include "fveq2.mm"
include "cbvmptv.mm"
include "syl5eqel.mm"
include "cnmpt21.mm"
include "eqeltrrd.mm"
include "cnmpt2nd.mm"
include "cnmpt1t.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "cnmptk1p.mm"
include "syl5eqelr.mm"
include "cnmpt2k.mm"
include "xkocnv.mm"
include "fveq12d.mm"
include "mpteq2i.mm"
include "nllytop.mm"
include "xkotop.mm"
include "xp2nd.mm"
include "ffvelrnd.mm"
include "eqeltrd.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem xkohmeo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  assume xkohmeo.x: |- ( ph -> J e. ( TopOn ` X ) )
  assume xkohmeo.y: |- ( ph -> K e. ( TopOn ` Y ) )
  assume xkohmeo.f: |- F = ( f e. ( ( J tX K ) Cn L ) |-> ( x e. X |-> ( y e. Y |-> ( x f y ) ) ) )
  assume xkohmeo.j: |- ( ph -> J e. N-Locally Comp )
  assume xkohmeo.k: |- ( ph -> K e. N-Locally Comp )
  assume xkohmeo.l: |- ( ph -> L e. Top )

  disjoint f x
  disjoint f y
  disjoint J f
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K f
  disjoint K x
  disjoint K y
  disjoint f ph
  disjoint ph x
  disjoint ph y
  disjoint L f
  disjoint L x
  disjoint L y
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y x
  disjoint Y y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f t
  disjoint f u
  disjoint f w
  disjoint f z
  disjoint g t
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint J g
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint x z
  disjoint y z
  disjoint J z
  disjoint K g
  disjoint K t
  disjoint K u
  disjoint K w
  disjoint K z
  disjoint g ph
  disjoint ph t
  disjoint ph u
  disjoint ph w
  disjoint ph z
  disjoint L g
  disjoint L t
  disjoint L u
  disjoint L w
  disjoint L z
  disjoint X g
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X z
  disjoint Y g
  disjoint Y t
  disjoint Y u
  disjoint Y w
  disjoint Y z
  disjoint F g
  assert |- ( ph -> F e. ( ( L ^ko ( J tX K ) ) Homeo ( ( L ^ko K ) ^ko J ) ) )

  proof
    wph
    cF
    cL
    cJ
    cK
    ctx
    co
    #
    cxko
    co
    #
    cL
    cK
    cxko
    co
    #
    cJ
    cxko
    co
    #
    ccn
    co
    #
    wcel
    cF
    ccnv
    #
    @3
    @1
    ccn
    co
    #
    wcel
    cF
    @1
    @3
    chmeo
    co
    wcel
    wph
    cF
    vf
    @0
    cL
    ccn
    co
    #
    vx
    cX
    vy
    cY
    vx
    cv
    #
    vy
    cv
    #
    vf
    cv
    #
    co
    #
    cmpt
    #
    cmpt
    cmpt
    @4
    xkohmeo.f
    wph
    vf
    vx
    @12
    @1
    cJ
    @2
    @7
    cX
    wph
    @0
    ctop
    wcel
    #
    cL
    ctop
    wcel
    #
    @1
    @7
    ctopon
    cfv
    wcel
    #
    wph
    @0
    cX
    cY
    cxp
    #
    ctopon
    cfv
    wcel
    #
    @13
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @17
    xkohmeo.x
    xkohmeo.y
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    #
    @16
    @0
    topontop
    syl
    xkohmeo.l
    @0
    cL
    @1
    @1
    eqid
    xkotopon
    syl2anc
    #
    xkohmeo.x
    wph
    vf
    vx
    @7
    cX
    @12
    cmpt2
    vz
    @7
    cX
    cxp
    #
    vy
    cY
    vz
    cv
    #
    c2nd
    cfv
    #
    @9
    @23
    c1st
    cfv
    #
    co
    #
    cmpt
    #
    cmpt
    @1
    cJ
    ctx
    co
    #
    @2
    ccn
    co
    vf
    vx
    vz
    @7
    cX
    @27
    @12
    @23
    @10
    @8
    cop
    wceq
    #
    vy
    cY
    @26
    @11
    @29
    @24
    @8
    @9
    @9
    @25
    @10
    @10
    @8
    @23
    vf
    vex
    #
    vx
    vex
    #
    op1std
    #
    @10
    @8
    @23
    @30
    @31
    op2ndd
    #
    @29
    @9
    eqidd
    oveq123d
    mpteq2dv
    mpt2mpt
    wph
    vz
    vy
    @26
    @28
    cK
    cL
    @22
    cY
    wph
    @15
    @18
    @28
    @22
    ctopon
    cfv
    wcel
    #
    @21
    xkohmeo.x
    @1
    cJ
    @7
    cX
    txtopon
    syl2anc
    #
    xkohmeo.y
    wph
    vz
    vy
    @22
    cY
    @26
    cmpt2
    vw
    @22
    cY
    cxp
    #
    vw
    cv
    #
    c1st
    cfv
    #
    c2nd
    cfv
    #
    @37
    c2nd
    cfv
    #
    @38
    c1st
    cfv
    #
    co
    #
    cmpt
    @28
    cK
    ctx
    co
    #
    cL
    ccn
    co
    vz
    vy
    vw
    @22
    cY
    @42
    @26
    @37
    @23
    @9
    cop
    wceq
    #
    @39
    @24
    @40
    @9
    @41
    @25
    @44
    @38
    @23
    c1st
    @23
    @9
    @37
    vz
    vex
    #
    vy
    vex
    #
    op1std
    #
    fveq2d
    #
    @44
    @38
    @23
    c2nd
    @47
    fveq2d
    #
    @23
    @9
    @37
    @45
    @46
    op2ndd
    #
    oveq123d
    mpt2mpt
    wph
    vw
    vu
    vu
    cv
    #
    @41
    cfv
    #
    @39
    @40
    cop
    #
    @42
    @43
    @0
    cL
    @36
    @16
    cL
    cuni
    #
    wph
    @34
    @19
    @43
    @36
    ctopon
    cfv
    wcel
    @35
    xkohmeo.y
    @28
    cK
    @22
    cY
    txtopon
    syl2anc
    #
    @20
    wph
    @14
    cL
    @54
    ctopon
    cfv
    wcel
    #
    xkohmeo.l
    cL
    @54
    @54
    eqid
    toptopon
    sylib
    #
    wph
    cJ
    ccmp
    cnlly
    #
    wcel
    #
    cK
    @58
    wcel
    #
    @0
    @58
    wcel
    xkohmeo.j
    xkohmeo.k
    ccmp
    cJ
    cK
    vx
    vy
    @8
    @9
    txcmp
    txnlly
    syl2anc
    wph
    vz
    vy
    @22
    cY
    @25
    cmpt2
    #
    vw
    @36
    vu
    @16
    @52
    cmpt
    #
    cmpt
    #
    @43
    @1
    ccn
    co
    wph
    @61
    vw
    @36
    @41
    cmpt
    @63
    vz
    vy
    vw
    @22
    cY
    @41
    @25
    @48
    mpt2mpt
    wph
    vw
    @36
    @41
    @62
    wph
    @37
    @36
    wcel
    #
    wa
    #
    vu
    @16
    @54
    @41
    @65
    @17
    @56
    @41
    @7
    wcel
    #
    @16
    @54
    @41
    wf
    wph
    @17
    @64
    @20
    adantr
    wph
    @56
    @64
    @57
    adantr
    @65
    @38
    @22
    wcel
    #
    @66
    @64
    @67
    wph
    @37
    @22
    cY
    xp1st
    adantl
    @38
    @7
    cX
    xp1st
    syl
    @41
    @0
    cL
    @16
    @54
    cnf2
    syl3anc
    feqmptd
    mpteq2dva
    syl5eqr
    wph
    vz
    vy
    vt
    @23
    vt
    cv
    #
    c1st
    cfv
    #
    @25
    @28
    cK
    @28
    @1
    @22
    cY
    @22
    @35
    xkohmeo.y
    wph
    vz
    vy
    @28
    cK
    @22
    cY
    @35
    xkohmeo.y
    cnmpt1st
    #
    @35
    wph
    vt
    @22
    @69
    cmpt
    vz
    @22
    @25
    cmpt
    #
    @28
    @1
    ccn
    co
    #
    vt
    vz
    @22
    @69
    @25
    @68
    @23
    c1st
    fveq2
    #
    cbvmptv
    wph
    @71
    vf
    vx
    @7
    cX
    @10
    cmpt2
    @72
    vf
    vx
    vz
    @7
    cX
    @25
    @10
    @32
    mpt2mpt
    wph
    vf
    vx
    @1
    cJ
    @7
    cX
    @21
    xkohmeo.x
    cnmpt1st
    syl5eqel
    syl5eqel
    @73
    cnmpt21
    eqeltrrd
    wph
    vw
    @39
    @40
    @43
    cJ
    cK
    @36
    @55
    wph
    vw
    @36
    @39
    cmpt
    vz
    vy
    @22
    cY
    @24
    cmpt2
    @43
    cJ
    ccn
    co
    vz
    vy
    vw
    @22
    cY
    @39
    @24
    @49
    mpt2mpt
    wph
    vz
    vy
    vt
    @23
    @68
    c2nd
    cfv
    #
    @24
    @28
    cK
    @28
    cJ
    @22
    cY
    @22
    @35
    xkohmeo.y
    @70
    @35
    wph
    vt
    @22
    @74
    cmpt
    vz
    @22
    @24
    cmpt
    #
    @28
    cJ
    ccn
    co
    #
    vt
    vz
    @22
    @74
    @24
    @68
    @23
    c2nd
    fveq2
    #
    cbvmptv
    wph
    @75
    vf
    vx
    @7
    cX
    @8
    cmpt2
    @76
    vf
    vx
    vz
    @7
    cX
    @24
    @8
    @33
    mpt2mpt
    wph
    vf
    vx
    @1
    cJ
    @7
    cX
    @21
    xkohmeo.x
    cnmpt2nd
    syl5eqel
    syl5eqel
    @77
    cnmpt21
    syl5eqel
    wph
    vw
    @36
    @40
    cmpt
    vz
    vy
    @22
    cY
    @9
    cmpt2
    @43
    cK
    ccn
    co
    vz
    vy
    vw
    @22
    cY
    @40
    @9
    @50
    mpt2mpt
    wph
    vz
    vy
    @28
    cK
    @22
    cY
    @35
    xkohmeo.y
    cnmpt2nd
    syl5eqel
    cnmpt1t
    @51
    @53
    wceq
    @52
    @53
    @41
    cfv
    @42
    @51
    @53
    @41
    fveq2
    @39
    @40
    @41
    df-ov
    syl6eqr
    cnmptk1p
    syl5eqelr
    cnmpt2k
    syl5eqelr
    cnmpt2k
    syl5eqel
    wph
    @5
    vg
    cJ
    @2
    ccn
    co
    #
    vz
    @16
    @24
    @25
    vg
    cv
    #
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    @6
    wph
    @5
    vg
    @78
    vx
    vy
    cX
    cY
    @9
    @8
    @79
    cfv
    #
    cfv
    #
    cmpt2
    #
    cmpt
    @83
    wph
    vx
    vy
    vf
    vg
    cF
    cJ
    cK
    cL
    cX
    cY
    xkohmeo.x
    xkohmeo.y
    xkohmeo.f
    xkohmeo.j
    xkohmeo.k
    xkohmeo.l
    xkocnv
    vg
    @78
    @82
    @86
    vx
    vy
    vz
    cX
    cY
    @81
    @85
    @23
    @8
    @9
    cop
    wceq
    #
    @24
    @9
    @80
    @84
    @87
    @25
    @8
    @79
    @8
    @9
    @23
    @31
    @46
    op1std
    #
    fveq2d
    @8
    @9
    @23
    @31
    @46
    op2ndd
    #
    fveq12d
    mpt2mpt
    mpteq2i
    syl6eqr
    wph
    vg
    vz
    @81
    @3
    @0
    cL
    @78
    @16
    wph
    cJ
    ctop
    wcel
    #
    @2
    ctop
    wcel
    #
    @3
    @78
    ctopon
    cfv
    wcel
    #
    wph
    @59
    @90
    xkohmeo.j
    ccmp
    cJ
    nllytop
    syl
    wph
    cK
    ctop
    wcel
    #
    @14
    @91
    wph
    @60
    @93
    xkohmeo.k
    ccmp
    cK
    nllytop
    syl
    #
    xkohmeo.l
    cK
    cL
    xkotop
    syl2anc
    cJ
    @2
    @3
    @3
    eqid
    xkotopon
    syl2anc
    #
    @20
    wph
    vg
    vz
    @78
    @16
    @81
    cmpt2
    vw
    @78
    @16
    cxp
    #
    @40
    c2nd
    cfv
    #
    @40
    c1st
    cfv
    #
    @38
    cfv
    #
    cfv
    #
    cmpt
    @3
    @0
    ctx
    co
    #
    cL
    ccn
    co
    vg
    vz
    vw
    @78
    @16
    @100
    @81
    @37
    @79
    @23
    cop
    wceq
    #
    @97
    @24
    @99
    @80
    @102
    @98
    @25
    @38
    @79
    @79
    @23
    @37
    vg
    vex
    #
    @45
    op1std
    #
    @102
    @40
    @23
    c1st
    @79
    @23
    @37
    @103
    @45
    op2ndd
    #
    fveq2d
    #
    fveq12d
    @102
    @40
    @23
    c2nd
    @105
    fveq2d
    #
    fveq12d
    mpt2mpt
    wph
    vw
    vy
    @9
    @99
    cfv
    #
    @97
    @100
    @101
    cK
    cL
    @96
    cY
    @54
    wph
    @92
    @17
    @101
    @96
    ctopon
    cfv
    wcel
    @95
    @20
    @3
    @0
    @78
    @16
    txtopon
    syl2anc
    #
    xkohmeo.y
    @57
    xkohmeo.k
    wph
    vw
    @96
    @99
    cmpt
    vw
    @96
    vy
    cY
    @108
    cmpt
    #
    cmpt
    @101
    @2
    ccn
    co
    wph
    vw
    @96
    @99
    @110
    wph
    @37
    @96
    wcel
    #
    wa
    #
    vy
    cY
    @54
    @99
    @112
    @19
    @56
    @99
    cK
    cL
    ccn
    co
    #
    wcel
    cY
    @54
    @99
    wf
    wph
    @19
    @111
    xkohmeo.y
    adantr
    wph
    @56
    @111
    @57
    adantr
    @112
    cX
    @113
    @98
    @38
    @112
    @18
    @2
    @113
    ctopon
    cfv
    wcel
    #
    @38
    @78
    wcel
    #
    cX
    @113
    @38
    wf
    wph
    @18
    @111
    xkohmeo.x
    adantr
    wph
    @114
    @111
    wph
    @93
    @14
    @114
    @94
    xkohmeo.l
    cK
    cL
    @2
    @2
    eqid
    xkotopon
    syl2anc
    #
    adantr
    @111
    @115
    wph
    @37
    @78
    @16
    xp1st
    adantl
    @38
    cJ
    @2
    cX
    @113
    cnf2
    syl3anc
    #
    @112
    @40
    @16
    wcel
    #
    @98
    cX
    wcel
    @111
    @118
    wph
    @37
    @78
    @16
    xp2nd
    adantl
    @40
    cX
    cY
    xp1st
    syl
    ffvelrnd
    @99
    cK
    cL
    cY
    @54
    cnf2
    syl3anc
    feqmptd
    mpteq2dva
    wph
    vw
    vx
    @8
    @38
    cfv
    #
    @98
    @99
    @101
    cJ
    @2
    @96
    cX
    @113
    @109
    xkohmeo.x
    @116
    xkohmeo.j
    wph
    vg
    vz
    @78
    @16
    @79
    cmpt2
    #
    vw
    @96
    vx
    cX
    @119
    cmpt
    #
    cmpt
    #
    @101
    @3
    ccn
    co
    wph
    @120
    vw
    @96
    @38
    cmpt
    @122
    vg
    vz
    vw
    @78
    @16
    @38
    @79
    @104
    mpt2mpt
    wph
    vw
    @96
    @38
    @121
    @112
    vx
    cX
    @113
    @38
    @117
    feqmptd
    mpteq2dva
    syl5eqr
    wph
    vg
    vz
    @3
    @0
    @78
    @16
    @95
    @20
    cnmpt1st
    eqeltrrd
    wph
    vw
    @96
    @98
    cmpt
    vg
    vz
    @78
    @16
    @25
    cmpt2
    @101
    cJ
    ccn
    co
    vg
    vz
    vw
    @78
    @16
    @98
    @25
    @106
    mpt2mpt
    wph
    vg
    vz
    vt
    @23
    @69
    @25
    @3
    @0
    @0
    cJ
    @78
    @16
    @16
    @95
    @20
    wph
    vg
    vz
    @3
    @0
    @78
    @16
    @95
    @20
    cnmpt2nd
    #
    @20
    wph
    vt
    @16
    @69
    cmpt
    vz
    @16
    @25
    cmpt
    #
    @0
    cJ
    ccn
    co
    #
    vt
    vz
    @16
    @69
    @25
    @73
    cbvmptv
    wph
    @124
    vx
    vy
    cX
    cY
    @8
    cmpt2
    @125
    vx
    vy
    vz
    cX
    cY
    @25
    @8
    @88
    mpt2mpt
    wph
    vx
    vy
    cJ
    cK
    cX
    cY
    xkohmeo.x
    xkohmeo.y
    cnmpt1st
    syl5eqel
    syl5eqel
    @73
    cnmpt21
    syl5eqel
    @8
    @98
    @38
    fveq2
    cnmptk1p
    eqeltrrd
    wph
    vw
    @96
    @97
    cmpt
    vg
    vz
    @78
    @16
    @24
    cmpt2
    @101
    cK
    ccn
    co
    vg
    vz
    vw
    @78
    @16
    @97
    @24
    @107
    mpt2mpt
    wph
    vg
    vz
    vt
    @23
    @74
    @24
    @3
    @0
    @0
    cK
    @78
    @16
    @16
    @95
    @20
    @123
    @20
    wph
    vt
    @16
    @74
    cmpt
    vz
    @16
    @24
    cmpt
    #
    @0
    cK
    ccn
    co
    #
    vt
    vz
    @16
    @74
    @24
    @77
    cbvmptv
    wph
    @126
    vx
    vy
    cX
    cY
    @9
    cmpt2
    @127
    vx
    vy
    vz
    cX
    cY
    @24
    @9
    @89
    mpt2mpt
    wph
    vx
    vy
    cJ
    cK
    cX
    cY
    xkohmeo.x
    xkohmeo.y
    cnmpt2nd
    syl5eqel
    syl5eqel
    @77
    cnmpt21
    syl5eqel
    @9
    @97
    @99
    fveq2
    cnmptk1p
    syl5eqelr
    cnmpt2k
    eqeltrd
    cF
    @1
    @3
    ishmeo
    sylanbrc
end
