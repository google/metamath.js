include "wcel.mm"
include "ccrg.mm"
include "csubrg.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "cress.mm"
include "co.mm"
include "cmpl.mm"
include "cascl.mm"
include "ccom.mm"
include "cbs.mm"
include "cmap.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "wceq.mm"
include "cmvr.mm"
include "wa.mm"
include "cpws.mm"
include "crh.mm"
include "crio.mm"
include "ces.mm"
include "cvv.mm"
include "elex.mm"
include "csb.mm"
include "fveq2.mm"
include "adantl.mm"
include "csbeq1d.mm"
include "fvex.mm"
include "a1i.mm"
include "simplr.mm"
include "fveq2d.mm"
include "simpll.mm"
include "oveq1.mm"
include "ad2antlr.mm"
include "oveq12d.mm"
include "ovexd.mm"
include "simprr.mm"
include "simprl.mm"
include "coeq2d.mm"
include "xpeq1d.mm"
include "mpteq2dv.mm"
include "eqeq12d.mm"
include "oveq1d.mm"
include "mpteq1d.mm"
include "mpteq12dv.mm"
include "anbi12d.mm"
include "riotaeqbidv.mm"
include "anassrs.mm"
include "csbied.mm"
include "eqtrd.mm"
include "df-evls.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "fveq1d.mm"
include "sylan.mm"
include "syl5eq.mm"
include "3adant3.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "mpteq1.mm"
include "eqeq1d.mm"
include "eqid.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "wtru.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "oveq12i.mm"
include "wb.mm"
include "fveq2i.mm"
include "coeq2i.mm"
include "xpeq1i.mm"
include "mpteq2i.mm"
include "eqeq12i.mm"
include "mpteq12i.mm"
include "anbi12i.mm"
include "trud.mm"
include "syl6eqr.mm"
include "3ad2ant3.mm"

theorem evlsval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  assume evlsval.q: |- Q = ( ( I evalSub S ) ` R )
  assume evlsval.w: |- W = ( I mPoly U )
  assume evlsval.v: |- V = ( I mVar U )
  assume evlsval.u: |- U = ( S |`s R )
  assume evlsval.t: |- T = ( S ^s ( B ^m I ) )
  assume evlsval.b: |- B = ( Base ` S )
  assume evlsval.a: |- A = ( algSc ` W )
  assume evlsval.x: |- X = ( x e. R |-> ( ( B ^m I ) X. { x } ) )
  assume evlsval.y: |- Y = ( x e. I |-> ( g e. ( B ^m I ) |-> ( g ` x ) ) )

  disjoint I f
  disjoint I g
  disjoint I x
  disjoint f g
  disjoint f x
  disjoint g x
  disjoint R f
  disjoint R x
  disjoint S f
  disjoint S g
  disjoint S x
  disjoint T f
  disjoint W f
  disjoint I b
  disjoint I i
  disjoint I r
  disjoint I s
  disjoint I w
  disjoint b f
  disjoint b g
  disjoint b i
  disjoint b r
  disjoint b s
  disjoint b w
  disjoint b x
  disjoint f i
  disjoint f r
  disjoint f s
  disjoint f w
  disjoint g i
  disjoint g r
  disjoint g s
  disjoint g w
  disjoint i r
  disjoint i s
  disjoint i w
  disjoint i x
  disjoint r s
  disjoint r w
  disjoint r x
  disjoint s w
  disjoint s x
  disjoint w x
  disjoint R r
  disjoint S b
  disjoint S i
  disjoint S r
  disjoint S s
  disjoint S w
  assert |- ( ( I e. Z /\ S e. CRing /\ R e. ( SubRing ` S ) ) -> Q = ( iota_ f e. ( W RingHom T ) ( ( f o. A ) = X /\ ( f o. V ) = Y ) ) )

  proof
    cI
    cZ
    wcel
    #
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    #
    wcel
    #
    w3a
    cQ
    cR
    vr
    @2
    vf
    cv
    #
    cI
    cS
    vr
    cv
    #
    cress
    co
    #
    cmpl
    co
    #
    cascl
    cfv
    #
    ccom
    #
    vx
    @5
    cS
    cbs
    cfv
    #
    cI
    cmap
    co
    #
    vx
    cv
    #
    csn
    #
    cxp
    #
    cmpt
    #
    wceq
    #
    @4
    cI
    @6
    cmvr
    co
    #
    ccom
    #
    vx
    cI
    vg
    @11
    @12
    vg
    cv
    cfv
    #
    cmpt
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vf
    @7
    cS
    @11
    cpws
    co
    #
    crh
    co
    #
    crio
    #
    cmpt
    #
    cfv
    #
    @4
    cA
    ccom
    #
    cX
    wceq
    #
    @4
    cV
    ccom
    #
    cY
    wceq
    #
    wa
    #
    vf
    cW
    cT
    crh
    co
    #
    crio
    #
    @0
    @1
    cQ
    @28
    wceq
    @3
    @0
    @1
    wa
    cQ
    cR
    cI
    cS
    ces
    co
    #
    cfv
    #
    @28
    evlsval.q
    @0
    cI
    cvv
    wcel
    #
    @1
    @37
    @28
    wceq
    cI
    cZ
    elex
    @38
    @1
    wa
    cR
    @36
    @27
    vi
    vs
    cI
    cS
    cvv
    ccrg
    vb
    vs
    cv
    #
    cbs
    cfv
    #
    vr
    @39
    csubrg
    cfv
    #
    vw
    vi
    cv
    #
    @39
    @5
    cress
    co
    #
    cmpl
    co
    #
    @4
    vw
    cv
    #
    cascl
    cfv
    #
    ccom
    #
    vx
    @5
    vb
    cv
    #
    @42
    cmap
    co
    #
    @13
    cxp
    #
    cmpt
    #
    wceq
    #
    @4
    @42
    @43
    cmvr
    co
    #
    ccom
    #
    vx
    @42
    vg
    @49
    @19
    cmpt
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vf
    @45
    @39
    @49
    cpws
    co
    #
    crh
    co
    #
    crio
    #
    csb
    #
    cmpt
    #
    csb
    #
    @27
    ces
    @42
    cI
    wceq
    #
    @39
    cS
    wceq
    #
    wa
    #
    @64
    vb
    @10
    @63
    csb
    @27
    @67
    vb
    @40
    @10
    @63
    @66
    @40
    @10
    wceq
    @65
    @39
    cS
    cbs
    fveq2
    adantl
    csbeq1d
    @67
    vb
    @10
    @63
    @27
    cvv
    @10
    cvv
    wcel
    @67
    cS
    cbs
    fvex
    a1i
    @67
    @48
    @10
    wceq
    #
    wa
    #
    vr
    @41
    @62
    @2
    @26
    @69
    @39
    cS
    csubrg
    @65
    @66
    @68
    simplr
    fveq2d
    @69
    @62
    vw
    @7
    @61
    csb
    @26
    @69
    vw
    @44
    @7
    @61
    @69
    @42
    cI
    @43
    @6
    cmpl
    @65
    @66
    @68
    simpll
    @66
    @43
    @6
    wceq
    @65
    @68
    @39
    cS
    @5
    cress
    oveq1
    ad2antlr
    oveq12d
    csbeq1d
    @69
    vw
    @7
    @61
    @26
    cvv
    @69
    cI
    @6
    cmpl
    ovexd
    @67
    @68
    @45
    @7
    wceq
    #
    @61
    @26
    wceq
    @67
    @68
    @70
    wa
    #
    wa
    #
    @58
    @23
    vf
    @60
    @25
    @72
    @45
    @7
    @59
    @24
    crh
    @67
    @68
    @70
    simprr
    #
    @72
    @39
    cS
    @49
    @11
    cpws
    @65
    @66
    @71
    simplr
    #
    @72
    @48
    @10
    @42
    cI
    cmap
    @67
    @68
    @70
    simprl
    @65
    @66
    @71
    simpll
    #
    oveq12d
    #
    oveq12d
    oveq12d
    @72
    @52
    @16
    @57
    @22
    @72
    @47
    @9
    @51
    @15
    @72
    @46
    @8
    @4
    @72
    @45
    @7
    cascl
    @73
    fveq2d
    coeq2d
    @72
    vx
    @5
    @50
    @14
    @72
    @49
    @11
    @13
    @76
    xpeq1d
    mpteq2dv
    eqeq12d
    @72
    @54
    @18
    @56
    @21
    @72
    @53
    @17
    @4
    @72
    @42
    cI
    @43
    @6
    cmvr
    @75
    @72
    @39
    cS
    @5
    cress
    @74
    oveq1d
    oveq12d
    coeq2d
    @72
    vx
    @42
    @55
    cI
    @20
    @75
    @72
    vg
    @49
    @11
    @19
    @76
    mpteq1d
    mpteq12dv
    eqeq12d
    anbi12d
    riotaeqbidv
    anassrs
    csbied
    eqtrd
    mpteq12dv
    csbied
    eqtrd
    vx
    vw
    vf
    vg
    vi
    vs
    vr
    vb
    df-evls
    vr
    @2
    @26
    cS
    csubrg
    fvex
    mptex
    ovmpt2a
    fveq1d
    sylan
    syl5eq
    3adant3
    @3
    @0
    @28
    @35
    wceq
    @1
    @3
    @28
    @4
    cI
    cS
    cR
    cress
    co
    #
    cmpl
    co
    #
    cascl
    cfv
    #
    ccom
    #
    vx
    cR
    @14
    cmpt
    #
    wceq
    #
    @4
    cI
    @77
    cmvr
    co
    #
    ccom
    #
    @21
    wceq
    #
    wa
    #
    vf
    @78
    @24
    crh
    co
    #
    crio
    #
    @35
    vr
    cR
    @26
    @88
    @2
    @27
    @5
    cR
    wceq
    #
    @23
    @86
    vf
    @25
    @87
    @89
    @7
    @78
    @24
    crh
    @89
    @6
    @77
    cI
    cmpl
    @5
    cR
    cS
    cress
    oveq2
    #
    oveq2d
    #
    oveq1d
    @89
    @16
    @82
    @22
    @85
    @89
    @9
    @80
    @15
    @81
    @89
    @8
    @79
    @4
    @89
    @7
    @78
    cascl
    @91
    fveq2d
    coeq2d
    vx
    @5
    cR
    @14
    mpteq1
    eqeq12d
    @89
    @18
    @84
    @21
    @89
    @17
    @83
    @4
    @89
    @6
    @77
    cI
    cmvr
    @90
    oveq2d
    coeq2d
    eqeq1d
    anbi12d
    riotaeqbidv
    @27
    eqid
    @86
    vf
    @87
    riotaex
    fvmpt
    @35
    @88
    wceq
    wtru
    @33
    @86
    vf
    @34
    @87
    @34
    @87
    wceq
    wtru
    cW
    @78
    cT
    @24
    crh
    cW
    cI
    cU
    cmpl
    co
    @78
    evlsval.w
    cU
    @77
    cI
    cmpl
    evlsval.u
    oveq2i
    eqtri
    #
    cT
    cS
    cB
    cI
    cmap
    co
    #
    cpws
    co
    @24
    evlsval.t
    @93
    @11
    cS
    cpws
    cB
    @10
    cI
    cmap
    evlsval.b
    oveq1i
    #
    oveq2i
    eqtri
    oveq12i
    a1i
    @33
    @86
    wb
    wtru
    @30
    @82
    @32
    @85
    @29
    @80
    cX
    @81
    cA
    @79
    @4
    cA
    cW
    cascl
    cfv
    @79
    evlsval.a
    cW
    @78
    cascl
    @92
    fveq2i
    eqtri
    coeq2i
    cX
    vx
    cR
    @93
    @13
    cxp
    #
    cmpt
    @81
    evlsval.x
    vx
    cR
    @95
    @14
    @93
    @11
    @13
    @94
    xpeq1i
    mpteq2i
    eqtri
    eqeq12i
    @31
    @84
    cY
    @21
    cV
    @83
    @4
    cV
    cI
    cU
    cmvr
    co
    @83
    evlsval.v
    cU
    @77
    cI
    cmvr
    evlsval.u
    oveq2i
    eqtri
    coeq2i
    cY
    vx
    cI
    vg
    @93
    @19
    cmpt
    #
    cmpt
    @21
    evlsval.y
    vx
    cI
    @96
    @20
    vg
    @93
    @19
    @11
    @19
    @94
    @19
    eqid
    mpteq12i
    mpteq2i
    eqtri
    eqeq12i
    anbi12i
    a1i
    riotaeqbidv
    trud
    syl6eqr
    3ad2ant3
    eqtrd
end
