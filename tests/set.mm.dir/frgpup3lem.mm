include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "wfn.mm"
include "ghmf.mm"
include "ffn.mm"
include "3syl.mm"
include "frgpup1.mm"
include "cv.mm"
include "cqs.mm"
include "cfv.mm"
include "wceq.mm"
include "wss.mm"
include "cbs.mm"
include "c2o.mm"
include "cxp.mm"
include "cfrmd.mm"
include "cvv.mm"
include "cqus.mm"
include "eqid.mm"
include "frgpval.mm"
include "syl.mm"
include "cword.mm"
include "cid.mm"
include "con0.mm"
include "2on.mm"
include "xpexg.mm"
include "sylancl.mm"
include "wrdexg.mm"
include "fvi.mm"
include "syl5eq.mm"
include "frmdbas.mm"
include "eqtr4d.mm"
include "cefg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fvexd.mm"
include "qusbas.mm"
include "syl6reqr.mm"
include "eqimss.mm"
include "sselda.mm"
include "cec.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "wa.mm"
include "cmpt.mm"
include "cvrmd.mm"
include "ccom.mm"
include "cgsu.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "cs1.mm"
include "cop.mm"
include "wrex.mm"
include "simpr.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "wrdf.mm"
include "ffvelrnda.mm"
include "elxp2.mm"
include "sylib.mm"
include "wi.mm"
include "c0.mm"
include "cif.mm"
include "weq.mm"
include "fveq2d.mm"
include "ifeq12d.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "ifex.mm"
include "ovmpt2.mm"
include "adantl.mm"
include "c1o.mm"
include "wo.mm"
include "cpr.mm"
include "elpri.mm"
include "df2o3.mm"
include "eleq2s.mm"
include "fveq1d.mm"
include "vrgpf.mm"
include "fvco3.mm"
include "sylan.mm"
include "eqtr3d.mm"
include "iftrue.mm"
include "opeq2d.mm"
include "s1eqd.mm"
include "eceq1d.mm"
include "vrgpval.mm"
include "3eqtr4d.mm"
include "cminusg.mm"
include "ghminv.mm"
include "syl2anc.mm"
include "wne.mm"
include "1n0.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "ifnefalse.mm"
include "vrgpinv.mm"
include "jaodan.mm"
include "sylan2.mm"
include "anasss.mm"
include "eqtrd.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "s1eq.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "ad2antrr.mm"
include "mpd.mm"
include "mpteq2dva.mm"
include "frgpuptf.mm"
include "fcompt.mm"
include "s1cld.mm"
include "eleqtrrd.mm"
include "frgpeccl.mm"
include "feqmptd.mm"
include "vrmdfval.mm"
include "fmptco.mm"
include "eqidd.mm"
include "eceq1.mm"
include "oveq2d.mm"
include "frgpupval.mm"
include "cmhm.mm"
include "ghmmhm.mm"
include "vrmdf.mm"
include "feq3d.mm"
include "mpbird.mm"
include "wrdco.mm"
include "mpteq1d.mm"
include "frgpmhm.mm"
include "eqeltrd.mm"
include "mhmf.mm"
include "feq2d.mm"
include "gsumwmhm.mm"
include "frmdgsum.mm"
include "wrdeq.mm"
include "wer.mm"
include "efger.mm"
include "divsfval.mm"
include "3eqtr3d.mm"
include "eqtr2d.mm"
include "ectocld.mm"
include "syldan.mm"
include "eqfnfvd.mm"

theorem frgpup3lem
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.sm: class .~
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let cA: class A
  let vc: setvar c
  let vh: setvar h
  let vt: setvar t
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let cC: class C
  let vi: setvar i
  let vj: setvar j
  let vw: setvar w
  let cM: class M
  assume frgpup.b: |- B = ( Base ` H )
  assume frgpup.n: |- N = ( invg ` H )
  assume frgpup.t: |- T = ( y e. I , z e. 2o |-> if ( z = (/) , ( F ` y ) , ( N ` ( F ` y ) ) ) )
  assume frgpup.h: |- ( ph -> H e. Grp )
  assume frgpup.i: |- ( ph -> I e. V )
  assume frgpup.a: |- ( ph -> F : I --> B )
  assume frgpup.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume frgpup.r: |- .~ = ( ~FG ` I )
  assume frgpup.g: |- G = ( freeGrp ` I )
  assume frgpup.x: |- X = ( Base ` G )
  assume frgpup.e: |- E = ran ( g e. W |-> <. [ g ] .~ , ( H gsum ( T o. g ) ) >. )
  assume frgpup.u: |- U = ( varFGrp ` I )
  assume frgpup3.k: |- ( ph -> K e. ( G GrpHom H ) )
  assume frgpup3.e: |- ( ph -> ( K o. U ) = F )

  disjoint g y
  disjoint g z
  disjoint y z
  disjoint H g
  disjoint F y
  disjoint F z
  disjoint N y
  disjoint N z
  disjoint B g
  disjoint B y
  disjoint B z
  disjoint T g
  disjoint .~ g
  disjoint g ph
  disjoint ph y
  disjoint ph z
  disjoint I y
  disjoint I z
  disjoint W g
  disjoint a b
  disjoint a g
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b g
  disjoint b u
  disjoint b v
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint g u
  disjoint g v
  disjoint A g
  disjoint u v
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A y
  disjoint A z
  disjoint a c
  disjoint a h
  disjoint a t
  disjoint E a
  disjoint c h
  disjoint c t
  disjoint c u
  disjoint E c
  disjoint h t
  disjoint h u
  disjoint E h
  disjoint t u
  disjoint E t
  disjoint E u
  disjoint a n
  disjoint a r
  disjoint a x
  disjoint H a
  disjoint b c
  disjoint b h
  disjoint b n
  disjoint b r
  disjoint b t
  disjoint b x
  disjoint H b
  disjoint c g
  disjoint c n
  disjoint c r
  disjoint c v
  disjoint c x
  disjoint H c
  disjoint g h
  disjoint g n
  disjoint g r
  disjoint g t
  disjoint g x
  disjoint h n
  disjoint h r
  disjoint h v
  disjoint h x
  disjoint H h
  disjoint n r
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint H n
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint H r
  disjoint t v
  disjoint t x
  disjoint H t
  disjoint u x
  disjoint H u
  disjoint v x
  disjoint H v
  disjoint H x
  disjoint C u
  disjoint C v
  disjoint a i
  disjoint a j
  disjoint a w
  disjoint K a
  disjoint i j
  disjoint i n
  disjoint i t
  disjoint i w
  disjoint K i
  disjoint j n
  disjoint j t
  disjoint j w
  disjoint K j
  disjoint n w
  disjoint K n
  disjoint t w
  disjoint K t
  disjoint K w
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint B a
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint G a
  disjoint c w
  disjoint G c
  disjoint G t
  disjoint u w
  disjoint G u
  disjoint G w
  disjoint T a
  disjoint b i
  disjoint b j
  disjoint T b
  disjoint g i
  disjoint g j
  disjoint h i
  disjoint h j
  disjoint T h
  disjoint i r
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint T i
  disjoint j r
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint T j
  disjoint T n
  disjoint T r
  disjoint T u
  disjoint T v
  disjoint T x
  disjoint .~ a
  disjoint b w
  disjoint .~ b
  disjoint g w
  disjoint h w
  disjoint .~ h
  disjoint .~ i
  disjoint .~ j
  disjoint .~ n
  disjoint r w
  disjoint .~ r
  disjoint .~ t
  disjoint .~ u
  disjoint w x
  disjoint .~ w
  disjoint .~ x
  disjoint a ph
  disjoint b ph
  disjoint c i
  disjoint c j
  disjoint c ph
  disjoint h ph
  disjoint i y
  disjoint i z
  disjoint i ph
  disjoint j y
  disjoint j z
  disjoint j ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint I a
  disjoint I b
  disjoint I i
  disjoint I j
  disjoint I n
  disjoint r y
  disjoint r z
  disjoint I r
  disjoint I w
  disjoint I x
  disjoint V w
  disjoint W a
  disjoint W b
  disjoint W h
  disjoint W n
  disjoint W r
  disjoint W t
  disjoint W u
  disjoint v w
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X n
  disjoint X u
  disjoint X w
  assert |- ( ph -> K = E )

  proof
    wph
    va
    cX
    cK
    cE
    wph
    cK
    cG
    cH
    cghm
    co
    #
    wcel
    #
    cX
    cB
    cK
    wf
    #
    cK
    cX
    wfn
    frgpup3.k
    cG
    cH
    cK
    cX
    cB
    frgpup.x
    frgpup.b
    ghmf
    #
    cX
    cB
    cK
    ffn
    3syl
    wph
    cE
    @0
    wcel
    cX
    cB
    cE
    wf
    cE
    cX
    wfn
    wph
    vy
    vz
    cB
    c.sm
    cT
    vg
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    cW
    cX
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpup.w
    frgpup.r
    frgpup.g
    frgpup.x
    frgpup.e
    frgpup1
    cG
    cH
    cE
    cX
    cB
    frgpup.x
    frgpup.b
    ghmf
    cX
    cB
    cE
    ffn
    3syl
    wph
    va
    cv
    #
    cX
    wcel
    @4
    cW
    c.sm
    cqs
    #
    wcel
    @4
    cK
    cfv
    #
    @4
    cE
    cfv
    #
    wceq
    #
    wph
    cX
    @5
    @4
    wph
    cX
    @5
    wceq
    cX
    @5
    wss
    wph
    @5
    cG
    cbs
    cfv
    cX
    wph
    c.sm
    cI
    c2o
    cxp
    #
    cfrmd
    cfv
    #
    cG
    cW
    cvv
    cvv
    wph
    cI
    cV
    wcel
    #
    cG
    @10
    c.sm
    cqus
    co
    wceq
    frgpup.i
    c.sm
    cG
    cI
    @10
    cV
    frgpup.g
    @10
    eqid
    #
    frgpup.r
    frgpval
    syl
    wph
    cW
    @9
    cword
    #
    @10
    cbs
    cfv
    #
    wph
    cW
    @13
    cid
    cfv
    #
    @13
    frgpup.w
    wph
    @9
    cvv
    wcel
    #
    @13
    cvv
    wcel
    @15
    @13
    wceq
    wph
    @11
    c2o
    con0
    wcel
    #
    @16
    frgpup.i
    2on
    cI
    c2o
    cV
    con0
    xpexg
    #
    sylancl
    #
    @9
    cvv
    wrdexg
    @13
    cvv
    fvi
    3syl
    syl5eq
    #
    wph
    @16
    @14
    @13
    wceq
    #
    @19
    @14
    @9
    @10
    cvv
    @12
    @14
    eqid
    #
    frmdbas
    syl
    #
    eqtr4d
    #
    c.sm
    cvv
    wcel
    wph
    c.sm
    cI
    cefg
    cfv
    cvv
    frgpup.r
    cI
    cefg
    fvex
    eqeltri
    a1i
    wph
    @9
    cfrmd
    fvexd
    qusbas
    frgpup.x
    syl6reqr
    cX
    @5
    eqimss
    syl
    sselda
    vt
    cv
    #
    c.sm
    cec
    #
    cK
    cfv
    #
    @26
    cE
    cfv
    #
    wceq
    @8
    wph
    vt
    @4
    cW
    c.sm
    @5
    @5
    eqid
    @26
    @4
    wceq
    @27
    @6
    @28
    @7
    @26
    @4
    cK
    fveq2
    @26
    @4
    cE
    fveq2
    eqeq12d
    wph
    @25
    cW
    wcel
    #
    wa
    #
    @28
    cG
    vw
    cW
    vw
    cv
    #
    c.sm
    cec
    #
    cmpt
    #
    @9
    cvrmd
    cfv
    #
    @25
    ccom
    #
    ccom
    #
    cgsu
    co
    #
    cK
    cfv
    #
    @27
    @30
    cH
    cT
    @25
    ccom
    #
    cgsu
    co
    cH
    cK
    @36
    ccom
    #
    cgsu
    co
    #
    @28
    @38
    @30
    @39
    @40
    cH
    cgsu
    @30
    vn
    cc0
    @25
    chash
    cfv
    cfzo
    co
    #
    vn
    cv
    #
    @25
    cfv
    #
    cT
    cfv
    #
    cmpt
    #
    vn
    @42
    @44
    cs1
    #
    c.sm
    cec
    #
    cK
    cfv
    #
    cmpt
    @39
    @40
    @30
    vn
    @42
    @45
    @49
    @30
    @43
    @42
    wcel
    #
    wa
    #
    @44
    vi
    cv
    #
    vj
    cv
    #
    cop
    #
    wceq
    #
    vj
    c2o
    wrex
    vi
    cI
    wrex
    #
    @45
    @49
    wceq
    #
    @51
    @44
    @9
    wcel
    @56
    @30
    @42
    @9
    @43
    @25
    @30
    @25
    @13
    wcel
    #
    @42
    @9
    @25
    wf
    #
    @30
    @25
    cW
    @13
    wph
    @29
    simpr
    wph
    cW
    @13
    wceq
    #
    @29
    @20
    adantr
    #
    eleqtrd
    #
    @9
    @25
    wrdf
    syl
    #
    ffvelrnda
    #
    vi
    vj
    @44
    cI
    c2o
    elxp2
    sylib
    wph
    @56
    @57
    wi
    @29
    @50
    wph
    @55
    @57
    vi
    vj
    cI
    c2o
    wph
    @52
    cI
    wcel
    #
    @53
    c2o
    wcel
    #
    wa
    #
    wa
    #
    @57
    @55
    @52
    @53
    cT
    co
    #
    @54
    cs1
    #
    c.sm
    cec
    #
    cK
    cfv
    #
    wceq
    @68
    @69
    @53
    c0
    wceq
    #
    @52
    cF
    cfv
    #
    @74
    cN
    cfv
    #
    cif
    #
    @72
    @67
    @69
    @76
    wceq
    wph
    vy
    vz
    @52
    @53
    cI
    c2o
    vz
    cv
    #
    c0
    wceq
    #
    vy
    cv
    #
    cF
    cfv
    #
    @80
    cN
    cfv
    #
    cif
    @76
    cT
    @78
    @74
    @75
    cif
    vy
    vi
    weq
    #
    @78
    @80
    @74
    @81
    @75
    @79
    @52
    cF
    fveq2
    #
    @82
    @80
    @74
    cN
    @83
    fveq2d
    ifeq12d
    vz
    vj
    weq
    @78
    @73
    @74
    @75
    @77
    @53
    c0
    eqeq1
    ifbid
    frgpup.t
    @73
    @74
    @75
    @52
    cF
    fvex
    @74
    cN
    fvex
    ifex
    ovmpt2
    adantl
    wph
    @65
    @66
    @76
    @72
    wceq
    #
    @66
    wph
    @65
    wa
    #
    @73
    @53
    c1o
    wceq
    #
    wo
    #
    @84
    @87
    @53
    c0
    c1o
    cpr
    c2o
    @53
    c0
    c1o
    elpri
    df2o3
    eleq2s
    @85
    @73
    @84
    @86
    @85
    @73
    wa
    #
    @74
    @52
    cU
    cfv
    #
    cK
    cfv
    #
    @76
    @72
    @85
    @74
    @90
    wceq
    @73
    @85
    @52
    cK
    cU
    ccom
    #
    cfv
    #
    @74
    @90
    @85
    @52
    @91
    cF
    wph
    @91
    cF
    wceq
    @65
    frgpup3.e
    adantr
    fveq1d
    wph
    cI
    cX
    cU
    wf
    #
    @65
    @92
    @90
    wceq
    wph
    @11
    @93
    frgpup.i
    c.sm
    cU
    cG
    cI
    cV
    cX
    frgpup.r
    frgpup.u
    frgpup.g
    frgpup.x
    vrgpf
    syl
    #
    cI
    cX
    @52
    cK
    cU
    fvco3
    sylan
    eqtr3d
    #
    adantr
    @73
    @76
    @74
    wceq
    @85
    @73
    @74
    @75
    iftrue
    adantl
    @88
    @71
    @89
    cK
    @88
    @71
    @52
    c0
    cop
    #
    cs1
    #
    c.sm
    cec
    #
    @89
    @88
    @70
    @97
    c.sm
    @88
    @54
    @96
    @88
    @53
    c0
    @52
    @85
    @73
    simpr
    opeq2d
    s1eqd
    eceq1d
    @85
    @89
    @98
    wceq
    #
    @73
    wph
    @11
    @65
    @99
    frgpup.i
    @52
    c.sm
    cU
    cI
    cV
    frgpup.r
    frgpup.u
    vrgpval
    sylan
    adantr
    eqtr4d
    fveq2d
    3eqtr4d
    @85
    @86
    wa
    #
    @75
    @89
    cG
    cminusg
    cfv
    #
    cfv
    #
    cK
    cfv
    #
    @76
    @72
    @85
    @75
    @103
    wceq
    @86
    @85
    @75
    @90
    cN
    cfv
    #
    @103
    @85
    @74
    @90
    cN
    @95
    fveq2d
    @85
    @1
    @89
    cX
    wcel
    @103
    @104
    wceq
    wph
    @1
    @65
    frgpup3.k
    adantr
    wph
    cI
    cX
    @52
    cU
    @94
    ffvelrnda
    cX
    cG
    cH
    cK
    @101
    cN
    @89
    frgpup.x
    @101
    eqid
    #
    frgpup.n
    ghminv
    syl2anc
    eqtr4d
    adantr
    @100
    @53
    c0
    wne
    #
    @76
    @75
    wceq
    @100
    @106
    c1o
    c0
    wne
    1n0
    @100
    @53
    c1o
    c0
    @85
    @86
    simpr
    #
    neeq1d
    mpbiri
    @53
    c0
    @74
    @75
    ifnefalse
    syl
    @100
    @71
    @102
    cK
    @100
    @71
    @52
    c1o
    cop
    #
    cs1
    #
    c.sm
    cec
    #
    @102
    @100
    @70
    @109
    c.sm
    @100
    @54
    @108
    @100
    @53
    c1o
    @52
    @107
    opeq2d
    s1eqd
    eceq1d
    @85
    @102
    @110
    wceq
    #
    @86
    wph
    @11
    @65
    @111
    frgpup.i
    @52
    c.sm
    cU
    cG
    cI
    @101
    cV
    frgpup.r
    frgpup.u
    frgpup.g
    @105
    vrgpinv
    sylan
    adantr
    eqtr4d
    fveq2d
    3eqtr4d
    jaodan
    sylan2
    anasss
    eqtrd
    @55
    @45
    @69
    @49
    @72
    @55
    @45
    @54
    cT
    cfv
    @69
    @44
    @54
    cT
    fveq2
    @52
    @53
    cT
    df-ov
    syl6eqr
    @55
    @48
    @71
    cK
    @55
    @47
    @70
    c.sm
    @44
    @54
    s1eq
    eceq1d
    fveq2d
    eqeq12d
    syl5ibrcom
    rexlimdvva
    ad2antrr
    mpd
    mpteq2dva
    @30
    @9
    cB
    cT
    wf
    #
    @59
    @39
    @46
    wceq
    wph
    @112
    @29
    wph
    vy
    vz
    cB
    cT
    cF
    cH
    cI
    cN
    cV
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpuptf
    adantr
    @63
    vn
    cT
    @25
    @42
    @9
    cB
    fcompt
    syl2anc
    @30
    vn
    vw
    @42
    cX
    @48
    @31
    cK
    cfv
    @49
    @36
    cK
    @51
    @47
    cW
    wcel
    @48
    cX
    wcel
    @51
    @47
    @13
    cW
    @51
    @44
    @9
    @64
    s1cld
    wph
    @60
    @29
    @50
    @20
    ad2antrr
    eleqtrrd
    #
    cX
    c.sm
    cG
    cI
    cW
    @47
    frgpup.g
    frgpup.r
    frgpup.w
    frgpup.x
    frgpeccl
    syl
    @30
    vn
    vw
    @42
    cW
    @47
    @32
    @48
    @35
    @33
    @113
    @30
    vn
    vw
    @42
    @9
    @44
    @31
    cs1
    #
    @47
    @25
    @34
    @64
    @30
    vn
    @42
    @9
    @25
    @63
    feqmptd
    @30
    @16
    @34
    vw
    @9
    @114
    cmpt
    wceq
    @30
    @11
    @17
    @16
    wph
    @11
    @29
    frgpup.i
    adantr
    #
    2on
    @18
    sylancl
    #
    @34
    vw
    @9
    cvv
    @34
    eqid
    #
    vrmdfval
    syl
    @31
    @44
    s1eq
    fmptco
    @30
    @33
    eqidd
    @31
    @47
    c.sm
    eceq1
    fmptco
    @30
    vw
    cX
    cB
    cK
    @30
    @1
    @2
    wph
    @1
    @29
    frgpup3.k
    adantr
    #
    @3
    syl
    feqmptd
    @31
    @48
    cK
    fveq2
    fmptco
    3eqtr4d
    oveq2d
    wph
    vy
    vz
    @25
    cB
    c.sm
    cT
    vg
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    cW
    cX
    frgpup.b
    frgpup.n
    frgpup.t
    frgpup.h
    frgpup.i
    frgpup.a
    frgpup.w
    frgpup.r
    frgpup.g
    frgpup.x
    frgpup.e
    frgpupval
    @30
    cK
    cG
    cH
    cmhm
    co
    wcel
    #
    @36
    cX
    cword
    wcel
    #
    @38
    @41
    wceq
    @30
    @1
    @119
    @118
    cG
    cH
    cK
    ghmmhm
    syl
    @30
    @35
    cW
    cword
    wcel
    #
    cW
    cX
    @33
    wf
    #
    @120
    @30
    @58
    @9
    cW
    @34
    wf
    #
    @121
    @62
    @30
    @123
    @9
    @13
    @34
    wf
    #
    @30
    @16
    @124
    @116
    @34
    @9
    cvv
    @117
    vrmdf
    syl
    #
    @30
    cW
    @13
    @34
    @9
    @61
    feq3d
    mpbird
    @9
    cW
    @34
    @25
    wrdco
    syl2anc
    @30
    @122
    @14
    cX
    @33
    wf
    #
    @30
    @33
    @10
    cG
    cmhm
    co
    #
    wcel
    #
    @126
    @30
    @33
    vw
    @14
    @32
    cmpt
    #
    @127
    @30
    vw
    cW
    @14
    @32
    wph
    cW
    @14
    wceq
    @29
    @24
    adantr
    #
    mpteq1d
    @30
    @11
    @129
    @127
    wcel
    @115
    vw
    c.sm
    @129
    cG
    cI
    @10
    cV
    @14
    @12
    @22
    frgpup.g
    frgpup.r
    @129
    eqid
    frgpmhm
    syl
    eqeltrd
    #
    @14
    cX
    @10
    cG
    @33
    @22
    frgpup.x
    mhmf
    syl
    @30
    cW
    @14
    cX
    @33
    @130
    feq2d
    mpbird
    cW
    cX
    @33
    @35
    wrdco
    syl2anc
    cX
    cK
    cG
    cH
    @36
    frgpup.x
    gsumwmhm
    syl2anc
    3eqtr4d
    @30
    @37
    @26
    cK
    @30
    @10
    @35
    cgsu
    co
    #
    @33
    cfv
    #
    @25
    @33
    cfv
    @37
    @26
    @30
    @132
    @25
    @33
    @30
    @16
    @58
    @132
    @25
    wceq
    @116
    @62
    @34
    @9
    @10
    cvv
    @25
    @12
    @117
    frmdgsum
    syl2anc
    fveq2d
    @30
    @128
    @35
    @14
    cword
    #
    wcel
    @133
    @37
    wceq
    @131
    @30
    @35
    @13
    cword
    #
    @134
    @30
    @58
    @124
    @35
    @135
    wcel
    @62
    @125
    @9
    @13
    @34
    @25
    wrdco
    syl2anc
    @30
    @21
    @134
    @135
    wceq
    wph
    @21
    @29
    @23
    adantr
    @14
    @13
    wrdeq
    syl
    eleqtrrd
    @14
    @33
    @10
    cG
    @35
    @22
    gsumwmhm
    syl2anc
    @30
    vw
    @25
    c.sm
    @33
    cW
    cW
    c.sm
    wer
    @30
    c.sm
    cI
    cW
    frgpup.w
    frgpup.r
    efger
    a1i
    cW
    cvv
    wcel
    @30
    cW
    @15
    cvv
    frgpup.w
    @13
    cid
    fvex
    eqeltri
    a1i
    @33
    eqid
    divsfval
    3eqtr3d
    fveq2d
    eqtr2d
    ectocld
    syldan
    eqfnfvd
end
