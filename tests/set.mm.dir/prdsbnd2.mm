include "ctotbnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cbnd.mm"
include "totbndbnd.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "cme.mm"
include "bndmet.mm"
include "0totbnd.mm"
include "syl5ibr.mm"
include "a1i.mm"
include "wne.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "wa.mm"
include "cbl.mm"
include "co.mm"
include "wss.mm"
include "cr.mm"
include "wrex.mm"
include "simprr.mm"
include "wb.mm"
include "cmpt.mm"
include "cprds.mm"
include "cds.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "fvexd.mm"
include "prdsmet.mm"
include "wfn.mm"
include "dffn5.mm"
include "sylib.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "3eltr4d.mm"
include "adantr.mm"
include "simpr.mm"
include "bnd2lem.mm"
include "syl2an.mm"
include "simprl.mm"
include "sseldd.mm"
include "ssbnd.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cxp.mm"
include "cres.mm"
include "xpss12.mm"
include "resabs1d.mm"
include "syl6eqr.mm"
include "crp.mm"
include "simpll.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "ne0i.mm"
include "syl.mm"
include "cxmt.mm"
include "cxr.mm"
include "ad2antrr.mm"
include "metxmet.mm"
include "rexrd.mm"
include "xbln0.mm"
include "syl3anc.mm"
include "elrpd.mm"
include "cress.mm"
include "cfn.mm"
include "ovex.mm"
include "fveq2.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "fnmpti.mm"
include "adantlr.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eleqtrd.mm"
include "prdsbascl.mm"
include "r19.21bi.mm"
include "simplrr.mm"
include "rpred.mm"
include "blbnd.mm"
include "xpeq12.mm"
include "anidms.mm"
include "reseq2d.mm"
include "eleq12d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "vtocl.mm"
include "mpbird.mm"
include "fvmpt.mm"
include "adantl.mm"
include "ressds.mm"
include "ax-mp.mm"
include "rpxr.mm"
include "ad2antll.mm"
include "blssm.mm"
include "ressbas2.mm"
include "eqtr4d.mm"
include "reseq1i.mm"
include "prdstotbnd.mm"
include "oveq2i.mm"
include "fveq2i.mm"
include "ressprdsds.mm"
include "cixp.mm"
include "ixpeq2dva.mm"
include "oveqdr.mm"
include "rpgt0.mm"
include "prdsbl.mm"
include "eqtrd.mm"
include "prdsbas3.mm"
include "3eqtr4rd.mm"
include "3eltr3d.mm"
include "syl12anc.mm"
include "totbndss.mm"
include "eqeltrrd.mm"
include "rexlimddv.mm"
include "exp32.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "pm2.61dne.mm"
include "impbid2.mm"

theorem prdsbnd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cE: class E
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vz: setvar z
  let va: setvar a
  let vr: setvar r
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vm: setvar m
  let vv: setvar v
  let vw: setvar w
  assume prdsbnd.y: |- Y = ( S Xs_ R )
  assume prdsbnd.b: |- B = ( Base ` Y )
  assume prdsbnd.v: |- V = ( Base ` ( R ` x ) )
  assume prdsbnd.e: |- E = ( ( dist ` ( R ` x ) ) |` ( V X. V ) )
  assume prdsbnd.d: |- D = ( dist ` Y )
  assume prdsbnd.s: |- ( ph -> S e. W )
  assume prdsbnd.i: |- ( ph -> I e. Fin )
  assume prdsbnd.r: |- ( ph -> R Fn I )
  assume prdsbnd2.c: |- C = ( D |` ( A X. A ) )
  assume prdsbnd2.e: |- ( ( ph /\ x e. I ) -> E e. ( Met ` V ) )
  assume prdsbnd2.m: |- ( ( ph /\ x e. I ) -> ( ( E |` ( y X. y ) ) e. ( TotBnd ` y ) <-> ( E |` ( y X. y ) ) e. ( Bnd ` y ) ) )

  disjoint D y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint B x
  disjoint B y
  disjoint E y
  disjoint ph x
  disjoint ph y
  disjoint I x
  disjoint I y
  disjoint S x
  disjoint V y
  disjoint Y x
  disjoint x z
  disjoint a r
  disjoint a z
  disjoint A a
  disjoint r z
  disjoint A r
  disjoint A z
  disjoint C a
  disjoint C r
  disjoint C z
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f r
  disjoint f v
  disjoint f y
  disjoint D f
  disjoint g k
  disjoint g m
  disjoint g r
  disjoint g v
  disjoint g y
  disjoint D g
  disjoint k m
  disjoint k r
  disjoint k v
  disjoint k y
  disjoint D k
  disjoint m r
  disjoint m v
  disjoint m y
  disjoint D m
  disjoint r v
  disjoint r y
  disjoint D r
  disjoint v y
  disjoint D v
  disjoint f w
  disjoint f x
  disjoint B f
  disjoint g w
  disjoint g x
  disjoint B g
  disjoint k w
  disjoint k x
  disjoint B k
  disjoint m w
  disjoint m x
  disjoint B m
  disjoint r w
  disjoint r x
  disjoint B r
  disjoint v w
  disjoint v x
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint f z
  disjoint E f
  disjoint g z
  disjoint E g
  disjoint k z
  disjoint E k
  disjoint E r
  disjoint w z
  disjoint E w
  disjoint y z
  disjoint E z
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a ph
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint ph r
  disjoint ph w
  disjoint I f
  disjoint I g
  disjoint I k
  disjoint I v
  disjoint I w
  disjoint V f
  disjoint V g
  disjoint V k
  disjoint V r
  disjoint V w
  disjoint V z
  assert |- ( ph -> ( C e. ( TotBnd ` A ) <-> C e. ( Bnd ` A ) ) )

  proof
    wph
    cC
    cA
    ctotbnd
    cfv
    #
    wcel
    #
    cC
    cA
    cbnd
    cfv
    wcel
    #
    cC
    cA
    totbndbnd
    wph
    @2
    @1
    wi
    #
    cA
    c0
    cA
    c0
    wceq
    #
    @3
    wi
    wph
    @2
    @1
    @4
    cC
    cA
    cme
    cfv
    wcel
    cC
    cA
    bndmet
    cC
    cA
    0totbnd
    syl5ibr
    a1i
    cA
    c0
    wne
    va
    cv
    #
    cA
    wcel
    #
    va
    wex
    wph
    @3
    va
    cA
    n0
    wph
    @6
    @3
    va
    wph
    @6
    @2
    @1
    wph
    @6
    @2
    wa
    #
    wa
    #
    cA
    @5
    vr
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    wss
    #
    @1
    vr
    cr
    @8
    @2
    @12
    vr
    cr
    wrex
    #
    wph
    @6
    @2
    simprr
    @8
    cD
    cB
    cme
    cfv
    #
    wcel
    #
    @5
    cB
    wcel
    #
    @2
    @13
    wb
    wph
    @15
    @7
    wph
    cS
    vx
    cI
    vx
    cv
    #
    cR
    cfv
    #
    cmpt
    #
    cprds
    co
    #
    cds
    cfv
    #
    @20
    cbs
    cfv
    #
    cme
    cfv
    cD
    @14
    wph
    vx
    @22
    @21
    @18
    cS
    cE
    cI
    cV
    cW
    @20
    cvv
    @20
    eqid
    #
    @22
    eqid
    #
    prdsbnd.v
    prdsbnd.e
    @21
    eqid
    prdsbnd.s
    prdsbnd.i
    wph
    @17
    cI
    wcel
    #
    wa
    #
    @17
    cR
    fvexd
    #
    prdsbnd2.e
    prdsmet
    wph
    cD
    cY
    cds
    cfv
    #
    @21
    prdsbnd.d
    wph
    cY
    @20
    cds
    wph
    cY
    cS
    cR
    cprds
    co
    @20
    prdsbnd.y
    wph
    cR
    @19
    cS
    cprds
    wph
    cR
    cI
    wfn
    cR
    @19
    wceq
    prdsbnd.r
    vx
    cI
    cR
    dffn5
    sylib
    oveq2d
    syl5eq
    #
    fveq2d
    syl5eq
    wph
    cB
    @22
    cme
    wph
    cB
    cY
    cbs
    cfv
    #
    @22
    prdsbnd.b
    wph
    cY
    @20
    cbs
    @29
    fveq2d
    syl5eq
    #
    fveq2d
    3eltr4d
    #
    adantr
    @8
    cA
    cB
    @5
    wph
    @15
    @2
    cA
    cB
    wss
    @7
    @32
    @6
    @2
    simpr
    cC
    cD
    cB
    cA
    prdsbnd2.c
    bnd2lem
    syl2an
    wph
    @6
    @2
    simprl
    #
    sseldd
    #
    @5
    cD
    cC
    cB
    cA
    vr
    prdsbnd2.c
    ssbnd
    syl2anc
    mpbid
    @8
    @9
    cr
    wcel
    #
    @12
    wa
    #
    wa
    #
    cD
    @11
    @11
    cxp
    #
    cres
    #
    cA
    cA
    cxp
    #
    cres
    #
    cC
    @0
    @37
    @41
    cD
    @40
    cres
    cC
    @37
    cD
    @40
    @38
    @37
    @12
    @12
    @40
    @38
    wss
    @8
    @35
    @12
    simprr
    #
    @42
    cA
    @11
    cA
    @11
    xpss12
    syl2anc
    resabs1d
    prdsbnd2.c
    syl6eqr
    @37
    @39
    @11
    ctotbnd
    cfv
    #
    wcel
    #
    @12
    @41
    @0
    wcel
    @37
    wph
    @16
    @9
    crp
    wcel
    #
    @44
    wph
    @7
    @36
    simpll
    @8
    @16
    @36
    @34
    adantr
    #
    @37
    @9
    @8
    @35
    @12
    simprl
    #
    @37
    @11
    c0
    wne
    #
    cc0
    @9
    clt
    wbr
    #
    @37
    @5
    @11
    wcel
    @48
    @37
    cA
    @11
    @5
    @42
    @8
    @6
    @36
    @33
    adantr
    sseldd
    @11
    @5
    ne0i
    syl
    @37
    cD
    cB
    cxmt
    cfv
    wcel
    #
    @16
    @9
    cxr
    wcel
    #
    @48
    @49
    wb
    @37
    @15
    @50
    wph
    @15
    @7
    @36
    @32
    ad2antrr
    cD
    cB
    metxmet
    syl
    @46
    @37
    @9
    @47
    rexrd
    cD
    @5
    @9
    cB
    xbln0
    syl3anc
    mpbid
    elrpd
    wph
    @16
    @45
    wa
    #
    wa
    #
    cS
    vy
    cI
    vy
    cv
    #
    cR
    cfv
    #
    @54
    @5
    cfv
    #
    @9
    @55
    cds
    cfv
    #
    @55
    cbs
    cfv
    #
    @58
    cxp
    #
    cres
    #
    cbl
    cfv
    #
    co
    #
    cress
    co
    #
    cmpt
    #
    cprds
    co
    #
    cds
    cfv
    #
    @65
    cbs
    cfv
    #
    ctotbnd
    cfv
    @39
    @43
    @53
    vx
    @67
    @66
    @64
    cS
    @17
    @64
    cfv
    #
    cds
    cfv
    #
    @68
    cbs
    cfv
    #
    @70
    cxp
    #
    cres
    #
    cI
    @70
    cW
    @65
    @65
    eqid
    @67
    eqid
    @70
    eqid
    @72
    eqid
    @66
    eqid
    wph
    cS
    cW
    wcel
    @52
    prdsbnd.s
    adantr
    #
    wph
    cI
    cfn
    wcel
    @52
    prdsbnd.i
    adantr
    #
    @64
    cI
    wfn
    @53
    vx
    cI
    @18
    @17
    @5
    cfv
    #
    @9
    cE
    cbl
    cfv
    #
    co
    #
    cress
    co
    #
    @64
    @18
    @77
    cress
    ovex
    #
    vy
    vx
    cI
    @63
    @78
    @54
    @17
    wceq
    #
    @55
    @18
    @62
    @77
    cress
    @54
    @17
    cR
    fveq2
    #
    @80
    @56
    @75
    @9
    @9
    @61
    @76
    @80
    @60
    cE
    cbl
    @80
    @60
    @18
    cds
    cfv
    #
    cV
    cV
    cxp
    #
    cres
    #
    cE
    @80
    @57
    @82
    @59
    @83
    @80
    @55
    @18
    cds
    @81
    fveq2d
    @80
    @58
    cV
    @80
    @58
    @18
    cbs
    cfv
    cV
    @80
    @55
    @18
    cbs
    @81
    fveq2d
    prdsbnd.v
    syl6eqr
    sqxpeqd
    reseq12d
    prdsbnd.e
    syl6eqr
    fveq2d
    @54
    @17
    @5
    fveq2
    @80
    @9
    eqidd
    oveq123d
    oveq12d
    #
    cbvmptv
    #
    fnmpti
    a1i
    @53
    @25
    wa
    #
    cE
    @77
    @77
    cxp
    #
    cres
    #
    @77
    ctotbnd
    cfv
    #
    @72
    @70
    ctotbnd
    cfv
    @87
    @89
    @90
    wcel
    #
    @89
    @77
    cbnd
    cfv
    #
    wcel
    #
    @87
    cE
    cV
    cxmt
    cfv
    wcel
    #
    @75
    cV
    wcel
    #
    @35
    @93
    @87
    cE
    cV
    cme
    cfv
    wcel
    #
    @94
    wph
    @25
    @96
    @52
    prdsbnd2.e
    adantlr
    cE
    cV
    metxmet
    syl
    #
    @53
    @95
    vx
    cI
    @53
    vx
    @22
    @18
    cS
    @5
    cI
    cV
    cW
    cfn
    cvv
    @20
    @23
    @24
    @73
    @74
    wph
    @18
    cvv
    wcel
    #
    vx
    cI
    wral
    @52
    wph
    @98
    vx
    cI
    @27
    ralrimiva
    adantr
    prdsbnd.v
    @53
    @5
    cB
    @22
    wph
    @16
    @45
    simprl
    #
    wph
    cB
    @22
    wceq
    @52
    @31
    adantr
    eleqtrd
    prdsbascl
    r19.21bi
    #
    @87
    @9
    wph
    @16
    @45
    @25
    simplrr
    rpred
    @9
    cE
    cV
    @75
    blbnd
    syl3anc
    wph
    @25
    @91
    @93
    wb
    #
    @52
    @26
    cE
    @54
    @54
    cxp
    #
    cres
    #
    @54
    ctotbnd
    cfv
    #
    wcel
    #
    @103
    @54
    cbnd
    cfv
    #
    wcel
    #
    wb
    #
    wi
    @26
    @101
    wi
    vy
    @77
    @75
    @9
    @76
    ovex
    #
    @54
    @77
    wceq
    #
    @108
    @101
    @26
    @110
    @105
    @91
    @107
    @93
    @110
    @103
    @89
    @104
    @90
    @110
    @102
    @88
    cE
    @110
    @102
    @88
    wceq
    @54
    @77
    @54
    @77
    xpeq12
    anidms
    reseq2d
    #
    @54
    @77
    ctotbnd
    fveq2
    eleq12d
    @110
    @103
    @89
    @106
    @92
    @111
    @54
    @77
    cbnd
    fveq2
    eleq12d
    bibi12d
    imbi2d
    prdsbnd2.m
    vtocl
    adantlr
    mpbird
    @87
    @72
    @82
    @88
    cres
    #
    @89
    @87
    @69
    @82
    @71
    @88
    @87
    @69
    @78
    cds
    cfv
    #
    @82
    @87
    @68
    @78
    cds
    @25
    @68
    @78
    wceq
    @53
    vy
    @17
    @63
    @78
    cI
    @64
    @85
    @64
    eqid
    @79
    fvmpt
    adantl
    #
    fveq2d
    @77
    cvv
    wcel
    #
    @82
    @113
    wceq
    @109
    @77
    @82
    @18
    @78
    cvv
    @78
    eqid
    #
    @82
    eqid
    ressds
    ax-mp
    syl6eqr
    @87
    @70
    @77
    @87
    @70
    @78
    cbs
    cfv
    #
    @77
    @87
    @68
    @78
    cbs
    @114
    fveq2d
    @87
    @77
    cV
    wss
    #
    @77
    @117
    wceq
    @87
    @94
    @95
    @51
    @118
    @97
    @100
    @53
    @51
    @25
    @45
    @51
    wph
    @16
    @9
    rpxr
    ad2antll
    #
    adantr
    cE
    @75
    @9
    cV
    blssm
    syl3anc
    #
    @77
    cV
    @78
    @18
    @116
    prdsbnd.v
    ressbas2
    syl
    #
    eqtr4d
    #
    sqxpeqd
    reseq12d
    @87
    @89
    @84
    @88
    cres
    @112
    cE
    @84
    @88
    prdsbnd.e
    reseq1i
    @87
    @82
    @88
    @83
    @87
    @118
    @118
    @88
    @83
    wss
    @120
    @120
    @77
    cV
    @77
    cV
    xpss12
    syl2anc
    resabs1d
    syl5eq
    eqtr4d
    @87
    @70
    @77
    ctotbnd
    @122
    fveq2d
    3eltr4d
    prdstotbnd
    @53
    @66
    cD
    cS
    vx
    cI
    @78
    cmpt
    #
    cprds
    co
    #
    cbs
    cfv
    #
    @125
    cxp
    #
    cres
    @39
    @53
    vx
    @77
    @125
    cD
    @18
    cS
    cS
    cW
    @66
    @124
    cI
    cW
    cfn
    cvv
    cY
    cvv
    wph
    cY
    @20
    wceq
    @52
    @29
    adantr
    @53
    @124
    eqidd
    @125
    eqid
    #
    prdsbnd.d
    @65
    @124
    cds
    @64
    @123
    cS
    cprds
    @86
    oveq2i
    #
    fveq2i
    @73
    @73
    @74
    @87
    @17
    cR
    fvexd
    #
    @115
    @87
    @109
    a1i
    ressprdsds
    @53
    @126
    @38
    cD
    @53
    @125
    @11
    @53
    vx
    cI
    @77
    cixp
    #
    vx
    cI
    @117
    cixp
    @11
    @125
    @53
    vx
    cI
    @77
    @117
    @121
    ixpeq2dva
    @53
    @11
    @5
    @9
    cS
    vy
    cI
    @55
    cmpt
    #
    cprds
    co
    #
    cds
    cfv
    #
    cbl
    cfv
    #
    co
    @130
    wph
    @52
    va
    vr
    @10
    @134
    wph
    cD
    @133
    cbl
    wph
    cD
    @28
    @133
    prdsbnd.d
    wph
    cY
    @132
    cds
    wph
    cY
    @20
    @132
    @29
    @131
    @19
    cS
    cprds
    vy
    vx
    cI
    @55
    @18
    @81
    cbvmptv
    oveq2i
    #
    syl6eqr
    #
    fveq2d
    syl5eq
    fveq2d
    oveqdr
    @53
    vx
    @9
    @132
    cbs
    cfv
    #
    @133
    @5
    @18
    cS
    cE
    cI
    cV
    cW
    @132
    cvv
    @135
    @137
    eqid
    prdsbnd.v
    prdsbnd.e
    @133
    eqid
    @73
    @74
    @129
    @97
    @53
    @5
    cB
    @137
    @99
    wph
    cB
    @137
    wceq
    @52
    wph
    cB
    @30
    @137
    prdsbnd.b
    wph
    cY
    @132
    cbs
    @136
    fveq2d
    syl5eq
    adantr
    eleqtrd
    @119
    @45
    @49
    wph
    @16
    @9
    rpgt0
    ad2antll
    prdsbl
    eqtrd
    @53
    vx
    @125
    @78
    cS
    cI
    @117
    cW
    cfn
    cvv
    @124
    @124
    eqid
    @127
    @73
    @74
    @53
    @78
    cvv
    wcel
    #
    vx
    cI
    @138
    @87
    @79
    a1i
    ralrimiva
    @117
    eqid
    prdsbas3
    3eqtr4rd
    #
    sqxpeqd
    reseq2d
    eqtrd
    @53
    @67
    @11
    ctotbnd
    @53
    @67
    @125
    @11
    @65
    @124
    cbs
    @128
    fveq2i
    @139
    syl5eq
    fveq2d
    3eltr3d
    syl12anc
    @42
    cA
    @39
    @11
    totbndss
    syl2anc
    eqeltrrd
    rexlimddv
    exp32
    exlimdv
    syl5bi
    pm2.61dne
    impbid2
end
