include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "wcel.mm"
include "cfv.mm"
include "cc0.mm"
include "co.mm"
include "cgsu.mm"
include "cn0.mm"
include "wf.mm"
include "cfn.mm"
include "wa.mm"
include "wb.mm"
include "psrbag.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "feqmptd.mm"
include "iftrue.mm"
include "adantl.mm"
include "wn.mm"
include "cdif.mm"
include "eldif.mm"
include "ifid.mm"
include "cvv.mm"
include "csupp.mm"
include "wss.mm"
include "frnnn0supp.mm"
include "syl2anc.mm"
include "eqimss.mm"
include "c0ex.mm"
include "a1i.mm"
include "suppssr.mm"
include "ifeq2d.mm"
include "syl5reqr.mm"
include "sylan2br.mm"
include "anassrs.mm"
include "pm2.61dan.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "eqeq2d.mm"
include "ifbid.mm"
include "mpteq2dv.mm"
include "cres.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "wi.mm"
include "simprd.mm"
include "wel.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "cur.mm"
include "cun.mm"
include "sseq1.mm"
include "noel.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "mpteq1.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ringidval.mm"
include "gsum0.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "mpl1.mm"
include "eqcomd.mm"
include "a1d.mm"
include "ssun1.mm"
include "sstr2.mm"
include "ax-mp.mm"
include "imim1i.mm"
include "cmulr.mm"
include "oveq1.mm"
include "caddc.mm"
include "cof.mm"
include "cbs.mm"
include "adantr.mm"
include "crg.mm"
include "ffvelrnda.mm"
include "0nn0.mm"
include "ifcl.mm"
include "sylancl.mm"
include "fmptd.mm"
include "simprll.mm"
include "eldifn.mm"
include "suppss2.mm"
include "ssfi.mm"
include "eqeltrrd.mm"
include "mpbir2and.mm"
include "ssun2.mm"
include "simprr.mm"
include "syl5ss.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "ffvelrnd.mm"
include "snifpsrbag.mm"
include "mplmonmul.mm"
include "mplcoe3.mm"
include "eqidd.mm"
include "offval2.mm"
include "nn0cnd.mm"
include "addid2d.mm"
include "elsni.mm"
include "simprlr.mm"
include "ad2antrr.mm"
include "eqneltrd.mm"
include "iftrued.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "simpr.mm"
include "sseldi.mm"
include "3eqtr4d.mm"
include "addid1d.mm"
include "velsn.mm"
include "sylnib.mm"
include "wo.mm"
include "biorf.mm"
include "elun.mm"
include "orcom.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "eqtrd.mm"
include "3eqtr3rd.mm"
include "ccntz.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "cmnd.mm"
include "mplring.mm"
include "ringmgp.mm"
include "cplusg.mm"
include "wral.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "cbvral2v.mm"
include "sylib.mm"
include "mplcoe5lem.mm"
include "sselda.mm"
include "mvrcl.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "adantlr.mm"
include "syldan.mm"
include "gsumzunsnd.mm"
include "syl5ibr.mm"
include "expr.mm"
include "a2d.mm"
include "syl5.mm"
include "expcom.mm"
include "findcard2s.mm"
include "mpcom.mm"
include "mpd.mm"
include "resmptd.mm"
include "ssid.mm"
include "eldifi.mm"
include "sylan2.mm"
include "mulg0.mm"
include "wfun.mm"
include "cfsupp.mm"
include "wbr.mm"
include "mptexg.mm"
include "funmpt.mm"
include "fvexd.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "gsumzres.mm"
include "3eqtr2d.mm"

theorem mplcoe5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let vf: setvar f
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vl: setvar l
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let vi: setvar i
  let vn: setvar n
  let vw: setvar w
  let cB: class B
  let cN: class N
  let cX: class X
  let c.x: class .x.
  assume mplcoe1.p: |- P = ( I mPoly R )
  assume mplcoe1.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplcoe1.z: |- .0. = ( 0g ` R )
  assume mplcoe1.o: |- .1. = ( 1r ` R )
  assume mplcoe1.i: |- ( ph -> I e. W )
  assume mplcoe2.g: |- G = ( mulGrp ` P )
  assume mplcoe2.m: |- .^ = ( .g ` G )
  assume mplcoe2.v: |- V = ( I mVar R )
  assume mplcoe5.r: |- ( ph -> R e. Ring )
  assume mplcoe5.y: |- ( ph -> Y e. D )
  assume mplcoe5.c: |- ( ph -> A. x e. I A. y e. I ( ( V ` y ) ( +g ` G ) ( V ` x ) ) = ( ( V ` x ) ( +g ` G ) ( V ` y ) ) )

  disjoint Y y
  disjoint ph y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint k x
  disjoint .^ k
  disjoint .^ x
  disjoint k y
  disjoint .1. k
  disjoint x y
  disjoint .1. x
  disjoint .1. y
  disjoint G k
  disjoint G x
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint I f
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint R f
  disjoint R y
  disjoint D k
  disjoint D x
  disjoint D y
  disjoint P k
  disjoint P x
  disjoint V k
  disjoint V x
  disjoint .0. f
  disjoint .0. k
  disjoint .0. x
  disjoint .0. y
  disjoint Y f
  disjoint Y k
  disjoint Y x
  disjoint Y y
  disjoint W k
  disjoint W y
  disjoint G y
  disjoint V y
  disjoint .^ y
  disjoint G l
  disjoint V l
  disjoint Y l
  disjoint l y
  disjoint .^ l
  disjoint l ph
  disjoint D a
  disjoint D b
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint I a
  disjoint I b
  disjoint P a
  disjoint R b
  disjoint V a
  disjoint V b
  disjoint W b
  disjoint Y a
  disjoint Y b
  disjoint a f
  disjoint b f
  disjoint a k
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b k
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint k z
  disjoint x z
  disjoint y z
  disjoint .^ a
  disjoint .^ b
  disjoint .0. a
  disjoint .0. b
  disjoint .1. a
  disjoint .1. b
  disjoint a ph
  disjoint b ph
  disjoint i k
  disjoint i n
  disjoint i w
  disjoint i x
  disjoint i z
  disjoint .^ i
  disjoint k n
  disjoint k w
  disjoint k z
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint .^ n
  disjoint w x
  disjoint w z
  disjoint .^ w
  disjoint x z
  disjoint .^ z
  disjoint i y
  disjoint .1. i
  disjoint n y
  disjoint .1. n
  disjoint w y
  disjoint .1. w
  disjoint y z
  disjoint .1. z
  disjoint B k
  disjoint G i
  disjoint G w
  disjoint G z
  disjoint f i
  disjoint f n
  disjoint f w
  disjoint f z
  disjoint I i
  disjoint I n
  disjoint I w
  disjoint I z
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint i ph
  disjoint n ph
  disjoint ph w
  disjoint ph z
  disjoint D i
  disjoint D n
  disjoint D w
  disjoint D z
  disjoint P i
  disjoint P w
  disjoint P z
  disjoint V i
  disjoint V n
  disjoint V w
  disjoint V z
  disjoint .0. i
  disjoint .0. n
  disjoint .0. w
  disjoint .0. z
  disjoint X f
  disjoint X k
  disjoint X n
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y i
  disjoint Y w
  disjoint Y z
  disjoint W i
  disjoint .x. k
  disjoint .x. w
  disjoint .x. x
  disjoint .x. z
  assert |- ( ph -> ( y e. D |-> if ( y = Y , .1. , .0. ) ) = ( G gsum ( k e. I |-> ( ( Y ` k ) .^ ( V ` k ) ) ) ) )

  proof
    wph
    vy
    cD
    vy
    cv
    #
    cY
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    vy
    cD
    @0
    vi
    cI
    vi
    cv
    #
    cY
    ccnv
    cn
    cima
    #
    wcel
    #
    @3
    cY
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cG
    vk
    cI
    vk
    cv
    #
    cY
    cfv
    #
    @12
    cV
    cfv
    #
    c.ex
    co
    #
    cmpt
    #
    cgsu
    co
    #
    wph
    vy
    cD
    @2
    @10
    wph
    @1
    @9
    c.1
    c.0
    wph
    cY
    @8
    @0
    wph
    cY
    vi
    cI
    @6
    cmpt
    @8
    wph
    vi
    cI
    cn0
    cY
    wph
    cI
    cn0
    cY
    wf
    #
    @4
    cfn
    wcel
    #
    wph
    cY
    cD
    wcel
    #
    @18
    @19
    wa
    #
    mplcoe5.y
    wph
    cI
    cW
    wcel
    #
    @20
    @21
    wb
    mplcoe1.i
    cD
    vf
    cY
    cI
    cW
    mplcoe1.d
    psrbag
    syl
    mpbid
    #
    simpld
    #
    feqmptd
    wph
    vi
    cI
    @7
    @6
    wph
    @3
    cI
    wcel
    #
    wa
    #
    @5
    @7
    @6
    wceq
    #
    @5
    @27
    @26
    @5
    @6
    cc0
    iftrue
    adantl
    wph
    @25
    @5
    wn
    #
    @27
    @25
    @28
    wa
    wph
    @3
    cI
    @4
    cdif
    #
    wcel
    #
    @27
    @3
    cI
    @4
    eldif
    wph
    @30
    wa
    #
    @6
    @5
    @6
    @6
    cif
    @7
    @5
    @6
    ifid
    @31
    @5
    @6
    cc0
    @6
    wph
    cI
    cn0
    cvv
    cY
    cW
    @4
    @3
    cc0
    @24
    wph
    cY
    cc0
    csupp
    co
    #
    @4
    wceq
    #
    @32
    @4
    wss
    wph
    @22
    @18
    @33
    mplcoe1.i
    @24
    cY
    cI
    cW
    frnnn0supp
    syl2anc
    @32
    @4
    eqimss
    syl
    #
    mplcoe1.i
    cc0
    cvv
    wcel
    wph
    c0ex
    a1i
    #
    suppssr
    ifeq2d
    syl5reqr
    sylan2br
    anassrs
    pm2.61dan
    mpteq2dva
    eqtr4d
    eqeq2d
    ifbid
    mpteq2dv
    wph
    @11
    cG
    vk
    @4
    @15
    cmpt
    #
    cgsu
    co
    #
    cG
    @16
    @4
    cres
    #
    cgsu
    co
    @17
    wph
    @4
    cI
    wss
    #
    @11
    @37
    wceq
    #
    wph
    cY
    cdm
    #
    @4
    cI
    cY
    cn
    cnvimass
    wph
    @18
    @41
    cI
    wceq
    @24
    cI
    cn0
    cY
    fdm
    syl
    syl5sseq
    #
    @19
    wph
    @39
    @40
    wi
    #
    wph
    @18
    @19
    @23
    simprd
    #
    wph
    vw
    cv
    #
    cI
    wss
    #
    vy
    cD
    @0
    vi
    cI
    vi
    vw
    wel
    #
    @6
    cc0
    cif
    #
    cmpt
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cG
    vk
    @45
    @15
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    #
    wi
    wph
    c0
    cI
    wss
    #
    vy
    cD
    @0
    cI
    cc0
    csn
    cxp
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cP
    cur
    cfv
    #
    wceq
    #
    wi
    #
    wi
    wph
    vx
    cv
    #
    cI
    wss
    #
    vy
    cD
    @0
    vi
    cI
    vi
    vx
    wel
    #
    @6
    cc0
    cif
    #
    cmpt
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cG
    vk
    @65
    @15
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    #
    wi
    wph
    @65
    vz
    cv
    #
    csn
    #
    cun
    #
    cI
    wss
    #
    vy
    cD
    @0
    vi
    cI
    @3
    @79
    wcel
    #
    @6
    cc0
    cif
    #
    cmpt
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cG
    vk
    @79
    @15
    cmpt
    #
    cgsu
    co
    #
    wceq
    #
    wi
    #
    wi
    wph
    @43
    wi
    vw
    vx
    vz
    @4
    @45
    c0
    wceq
    #
    @56
    @64
    wph
    @91
    @46
    @57
    @55
    @63
    @45
    c0
    cI
    sseq1
    @91
    @52
    @61
    @54
    @62
    @91
    vy
    cD
    @51
    @60
    @91
    @50
    @59
    c.1
    c.0
    @91
    @49
    @58
    @0
    @91
    @49
    vi
    cI
    cc0
    cmpt
    @58
    @91
    vi
    cI
    @48
    cc0
    @91
    @47
    @6
    cc0
    @91
    @47
    @3
    c0
    wcel
    @3
    noel
    @45
    c0
    @3
    eleq2
    mtbiri
    iffalsed
    mpteq2dv
    vi
    cI
    cc0
    fconstmpt
    syl6eqr
    eqeq2d
    ifbid
    mpteq2dv
    @91
    @54
    cG
    c0
    cgsu
    co
    @62
    @91
    @53
    c0
    cG
    cgsu
    @91
    @53
    vk
    c0
    @15
    cmpt
    c0
    vk
    @45
    c0
    @15
    mpteq1
    vk
    @15
    mpt0
    syl6eq
    oveq2d
    cG
    @62
    cP
    @62
    cG
    mplcoe2.g
    @62
    eqid
    #
    ringidval
    #
    gsum0
    syl6eq
    eqeq12d
    imbi12d
    imbi2d
    vw
    vx
    weq
    #
    @56
    @76
    wph
    @94
    @46
    @66
    @55
    @75
    @45
    @65
    cI
    sseq1
    @94
    @52
    @72
    @54
    @74
    @94
    vy
    cD
    @51
    @71
    @94
    @50
    @70
    c.1
    c.0
    @94
    @49
    @69
    @0
    @94
    vi
    cI
    @48
    @68
    @94
    @47
    @67
    @6
    cc0
    @45
    @65
    @3
    eleq2
    ifbid
    mpteq2dv
    eqeq2d
    ifbid
    mpteq2dv
    @94
    @53
    @73
    cG
    cgsu
    vk
    @45
    @65
    @15
    mpteq1
    oveq2d
    eqeq12d
    imbi12d
    imbi2d
    @45
    @79
    wceq
    #
    @56
    @90
    wph
    @95
    @46
    @80
    @55
    @89
    @45
    @79
    cI
    sseq1
    @95
    @52
    @86
    @54
    @88
    @95
    vy
    cD
    @51
    @85
    @95
    @50
    @84
    c.1
    c.0
    @95
    @49
    @83
    @0
    @95
    vi
    cI
    @48
    @82
    @95
    @47
    @81
    @6
    cc0
    @45
    @79
    @3
    eleq2
    ifbid
    mpteq2dv
    eqeq2d
    ifbid
    mpteq2dv
    @95
    @53
    @87
    cG
    cgsu
    vk
    @45
    @79
    @15
    mpteq1
    oveq2d
    eqeq12d
    imbi12d
    imbi2d
    @45
    @4
    wceq
    #
    @56
    @43
    wph
    @96
    @46
    @39
    @55
    @40
    @45
    @4
    cI
    sseq1
    @96
    @52
    @11
    @54
    @37
    @96
    vy
    cD
    @51
    @10
    @96
    @50
    @9
    c.1
    c.0
    @96
    @49
    @8
    @0
    @96
    vi
    cI
    @48
    @7
    @96
    @47
    @5
    @6
    cc0
    @45
    @4
    @3
    eleq2
    ifbid
    mpteq2dv
    eqeq2d
    ifbid
    mpteq2dv
    @96
    @53
    @36
    cG
    cgsu
    vk
    @45
    @4
    @15
    mpteq1
    oveq2d
    eqeq12d
    imbi12d
    imbi2d
    wph
    @63
    @57
    wph
    @62
    @61
    wph
    vy
    cD
    cP
    cR
    @62
    c.1
    vf
    cI
    cW
    c.0
    mplcoe1.p
    mplcoe1.d
    mplcoe1.z
    mplcoe1.o
    @92
    mplcoe1.i
    mplcoe5.r
    mpl1
    eqcomd
    a1d
    @65
    cfn
    wcel
    #
    vz
    vx
    wel
    wn
    #
    wa
    #
    wph
    @76
    @90
    wph
    @99
    @76
    @90
    wi
    @76
    @80
    @75
    wi
    wph
    @99
    wa
    #
    @90
    @80
    @66
    @75
    @65
    @79
    wss
    @80
    @66
    wi
    @65
    @78
    ssun1
    #
    @65
    @79
    cI
    sstr2
    ax-mp
    imim1i
    @100
    @80
    @75
    @89
    wph
    @99
    @80
    @75
    @89
    wi
    @75
    @89
    wph
    @99
    @80
    wa
    #
    wa
    #
    @72
    @77
    cY
    cfv
    #
    @77
    cV
    cfv
    #
    c.ex
    co
    #
    cP
    cmulr
    cfv
    #
    co
    #
    @74
    @106
    @107
    co
    #
    wceq
    @72
    @74
    @106
    @107
    oveq1
    @103
    @86
    @108
    @88
    @109
    @103
    @72
    vy
    cD
    @0
    vi
    cI
    vi
    vz
    weq
    #
    @104
    cc0
    cif
    #
    cmpt
    #
    wceq
    c.1
    c.0
    cif
    cmpt
    #
    @107
    co
    vy
    cD
    @0
    @69
    @112
    caddc
    cof
    co
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    @108
    @86
    @103
    vy
    cP
    cbs
    cfv
    #
    cD
    cP
    cR
    @107
    c.1
    vf
    cI
    cW
    @69
    @112
    c.0
    mplcoe1.p
    @117
    eqid
    #
    mplcoe1.z
    mplcoe1.o
    mplcoe1.d
    wph
    @22
    @102
    mplcoe1.i
    adantr
    #
    wph
    cR
    crg
    wcel
    #
    @102
    mplcoe5.r
    adantr
    #
    @103
    @69
    cD
    wcel
    #
    cI
    cn0
    @69
    wf
    #
    @69
    ccnv
    cn
    cima
    #
    cfn
    wcel
    #
    @103
    vi
    cI
    @68
    cn0
    @69
    @103
    @25
    wa
    #
    @6
    cn0
    wcel
    #
    cc0
    cn0
    wcel
    #
    @68
    cn0
    wcel
    #
    @103
    cI
    cn0
    @3
    cY
    wph
    @18
    @102
    @24
    adantr
    #
    ffvelrnda
    #
    0nn0
    @67
    @6
    cc0
    cn0
    ifcl
    sylancl
    #
    @69
    eqid
    fmptd
    #
    @103
    @69
    cc0
    csupp
    co
    #
    @124
    cfn
    @103
    @22
    @123
    @134
    @124
    wceq
    @119
    @133
    @69
    cI
    cW
    frnnn0supp
    syl2anc
    @103
    @97
    @134
    @65
    wss
    @134
    cfn
    wcel
    wph
    @97
    @98
    @80
    simprll
    #
    @103
    cI
    @68
    vi
    cW
    @65
    cc0
    @103
    @3
    cI
    @65
    cdif
    wcel
    #
    wa
    @67
    @6
    cc0
    @136
    @67
    wn
    @103
    @3
    cI
    @65
    eldifn
    adantl
    iffalsed
    @119
    suppss2
    @65
    @134
    ssfi
    syl2anc
    eqeltrrd
    @103
    @22
    @122
    @123
    @125
    wa
    wb
    @119
    cD
    vf
    @69
    cI
    cW
    mplcoe1.d
    psrbag
    syl
    mpbir2and
    @107
    eqid
    #
    @103
    @22
    @104
    cn0
    wcel
    #
    @112
    cD
    wcel
    @119
    @103
    cI
    cn0
    @77
    cY
    @130
    @103
    @78
    cI
    wss
    @77
    cI
    wcel
    @103
    @78
    @79
    cI
    @78
    @65
    ssun2
    #
    wph
    @99
    @80
    simprr
    #
    syl5ss
    @77
    cI
    vz
    vex
    snss
    sylibr
    #
    ffvelrnd
    #
    vi
    cD
    vf
    cI
    @104
    cW
    @77
    mplcoe1.d
    snifpsrbag
    syl2anc
    mplmonmul
    @103
    @113
    @106
    @72
    @107
    @103
    vy
    cD
    cP
    cR
    c.1
    vf
    vi
    c.ex
    cG
    cI
    @104
    cV
    cW
    @77
    c.0
    mplcoe1.p
    mplcoe1.d
    mplcoe1.z
    mplcoe1.o
    @119
    mplcoe2.g
    mplcoe2.m
    mplcoe2.v
    @121
    @141
    @142
    mplcoe3
    oveq2d
    @103
    vy
    cD
    @116
    @85
    @103
    @115
    @84
    c.1
    c.0
    @103
    @114
    @83
    @0
    @103
    @114
    vi
    cI
    @68
    @111
    caddc
    co
    #
    cmpt
    @83
    @103
    vi
    cI
    @68
    @111
    caddc
    @69
    @112
    cW
    cn0
    cn0
    @119
    @132
    @126
    @138
    @128
    @111
    cn0
    wcel
    @103
    @138
    @25
    @142
    adantr
    0nn0
    @110
    @104
    cc0
    cn0
    ifcl
    sylancl
    @103
    @69
    eqidd
    @103
    @112
    eqidd
    offval2
    @103
    vi
    cI
    @143
    @82
    @126
    @3
    @78
    wcel
    #
    @143
    @82
    wceq
    @126
    @144
    wa
    #
    cc0
    @6
    caddc
    co
    @6
    @143
    @82
    @145
    @6
    @145
    @6
    @126
    @127
    @144
    @131
    adantr
    nn0cnd
    addid2d
    @145
    @68
    cc0
    @111
    @6
    caddc
    @145
    @67
    @6
    cc0
    @145
    @3
    @77
    @65
    @144
    @110
    @126
    @3
    @77
    elsni
    adantl
    #
    @103
    @98
    @25
    @144
    wph
    @97
    @98
    @80
    simprlr
    #
    ad2antrr
    eqneltrd
    iffalsed
    @145
    @111
    @104
    @6
    @145
    @110
    @104
    cc0
    @146
    iftrued
    @145
    @3
    @77
    cY
    @146
    fveq2d
    eqtr4d
    oveq12d
    @145
    @81
    @6
    cc0
    @145
    @78
    @79
    @3
    @139
    @126
    @144
    simpr
    sseldi
    iftrued
    3eqtr4d
    @126
    @144
    wn
    #
    wa
    #
    @68
    cc0
    caddc
    co
    @68
    @143
    @82
    @149
    @68
    @149
    @68
    @126
    @129
    @148
    @132
    adantr
    nn0cnd
    addid1d
    @149
    @111
    cc0
    @68
    caddc
    @149
    @110
    @104
    cc0
    @149
    @144
    @110
    @126
    @148
    simpr
    vi
    @77
    velsn
    sylnib
    iffalsed
    oveq2d
    @149
    @81
    @67
    @6
    cc0
    @148
    @81
    @67
    wb
    @126
    @148
    @67
    @144
    @67
    wo
    #
    @81
    @144
    @67
    biorf
    @81
    @67
    @144
    wo
    @150
    @3
    @65
    @78
    elun
    @67
    @144
    orcom
    bitri
    syl6rbbr
    adantl
    ifbid
    3eqtr4d
    pm2.61dan
    mpteq2dva
    eqtrd
    eqeq2d
    ifbid
    mpteq2dv
    3eqtr3rd
    @103
    @65
    @117
    @107
    vk
    @87
    cG
    @77
    cI
    @15
    @106
    cG
    ccntz
    cfv
    #
    @117
    cP
    cG
    mplcoe2.g
    @118
    mgpbas
    #
    cP
    @107
    cG
    mplcoe2.g
    @137
    mgpplusg
    @151
    eqid
    #
    @87
    eqid
    wph
    cG
    cmnd
    wcel
    #
    @102
    wph
    cP
    crg
    wcel
    #
    @154
    wph
    @22
    @120
    @155
    mplcoe1.i
    mplcoe5.r
    cP
    cR
    cI
    cW
    mplcoe1.p
    mplring
    syl2anc
    cP
    cG
    mplcoe2.g
    ringmgp
    syl
    #
    adantr
    #
    @135
    @103
    va
    vb
    cD
    cP
    cR
    @79
    c.1
    vf
    vk
    c.ex
    cG
    cI
    cV
    cW
    cY
    c.0
    mplcoe1.p
    mplcoe1.d
    mplcoe1.z
    mplcoe1.o
    @119
    mplcoe2.g
    mplcoe2.m
    mplcoe2.v
    @121
    wph
    @20
    @102
    mplcoe5.y
    adantr
    wph
    vb
    cv
    #
    cV
    cfv
    #
    va
    cv
    #
    cV
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @161
    @159
    @162
    co
    #
    wceq
    #
    vb
    cI
    wral
    va
    cI
    wral
    #
    @102
    wph
    @0
    cV
    cfv
    #
    @65
    cV
    cfv
    #
    @162
    co
    #
    @168
    @167
    @162
    co
    #
    wceq
    #
    vy
    cI
    wral
    vx
    cI
    wral
    @166
    mplcoe5.c
    @171
    @165
    @167
    @161
    @162
    co
    #
    @161
    @167
    @162
    co
    #
    wceq
    vx
    vy
    va
    vb
    cI
    cI
    vx
    va
    weq
    #
    @169
    @172
    @170
    @173
    @174
    @168
    @161
    @167
    @162
    @65
    @160
    cV
    fveq2
    #
    oveq2d
    @174
    @168
    @161
    @167
    @162
    @175
    oveq1d
    eqeq12d
    vy
    vb
    weq
    #
    @172
    @163
    @173
    @164
    @176
    @167
    @159
    @161
    @162
    @0
    @158
    cV
    fveq2
    #
    oveq1d
    @176
    @167
    @159
    @161
    @162
    @177
    oveq2d
    eqeq12d
    cbvral2v
    sylib
    adantr
    @140
    mplcoe5lem
    @103
    vk
    vx
    wel
    @12
    cI
    wcel
    #
    @15
    @117
    wcel
    #
    @103
    @65
    cI
    @12
    @103
    @65
    @79
    cI
    @101
    @140
    syl5ss
    sselda
    wph
    @178
    @179
    @102
    wph
    @178
    wa
    #
    @154
    @13
    cn0
    wcel
    @14
    @117
    wcel
    #
    @179
    wph
    @154
    @178
    @156
    adantr
    wph
    cI
    cn0
    @12
    cY
    @24
    ffvelrnda
    @180
    @117
    cP
    cR
    cI
    cV
    cW
    @12
    mplcoe1.p
    mplcoe2.v
    @118
    wph
    @22
    @178
    mplcoe1.i
    adantr
    wph
    @120
    @178
    mplcoe5.r
    adantr
    wph
    @178
    simpr
    mvrcl
    #
    @117
    c.ex
    cG
    @13
    @14
    @152
    mplcoe2.m
    mulgnn0cl
    syl3anc
    #
    adantlr
    syldan
    @141
    @147
    @103
    @154
    @138
    @105
    @117
    wcel
    @106
    @117
    wcel
    @157
    @142
    @103
    @117
    cP
    cR
    cI
    cV
    cW
    @77
    mplcoe1.p
    mplcoe2.v
    @118
    @119
    @121
    @141
    mvrcl
    @117
    c.ex
    cG
    @104
    @105
    @152
    mplcoe2.m
    mulgnn0cl
    syl3anc
    vk
    vz
    weq
    #
    @15
    @106
    wceq
    @103
    @184
    @13
    @104
    @14
    @105
    c.ex
    @12
    @77
    cY
    fveq2
    @12
    @77
    cV
    fveq2
    oveq12d
    adantl
    gsumzunsnd
    eqeq12d
    syl5ibr
    expr
    a2d
    syl5
    expcom
    a2d
    findcard2s
    mpcom
    mpd
    wph
    @38
    @36
    cG
    cgsu
    wph
    vk
    cI
    @4
    @15
    @42
    resmptd
    oveq2d
    wph
    cI
    @117
    @16
    cG
    cW
    @4
    @62
    @151
    @152
    @93
    @153
    @156
    mplcoe1.i
    wph
    vk
    cI
    @15
    @117
    @16
    @183
    @16
    eqid
    fmptd
    wph
    vx
    vy
    cD
    cP
    cR
    cI
    c.1
    vf
    vk
    c.ex
    cG
    cI
    cV
    cW
    cY
    c.0
    mplcoe1.p
    mplcoe1.d
    mplcoe1.z
    mplcoe1.o
    mplcoe1.i
    mplcoe2.g
    mplcoe2.m
    mplcoe2.v
    mplcoe5.r
    mplcoe5.y
    mplcoe5.c
    cI
    cI
    wss
    wph
    cI
    ssid
    a1i
    mplcoe5lem
    wph
    cI
    @15
    vk
    cW
    @4
    @62
    wph
    @12
    @29
    wcel
    #
    wa
    #
    @15
    cc0
    @14
    c.ex
    co
    #
    @62
    @186
    @13
    cc0
    @14
    c.ex
    wph
    cI
    cn0
    cvv
    cY
    cW
    @4
    @12
    cc0
    @24
    @34
    mplcoe1.i
    @35
    suppssr
    oveq1d
    @186
    @181
    @187
    @62
    wceq
    @185
    wph
    @178
    @181
    @12
    cI
    @4
    eldifi
    @182
    sylan2
    @117
    c.ex
    cG
    @14
    @62
    @152
    @93
    mplcoe2.m
    mulg0
    syl
    eqtrd
    mplcoe1.i
    suppss2
    #
    wph
    @16
    cvv
    wcel
    #
    @16
    wfun
    #
    @62
    cvv
    wcel
    @19
    @16
    @62
    csupp
    co
    @4
    wss
    @16
    @62
    cfsupp
    wbr
    wph
    @22
    @189
    mplcoe1.i
    vk
    cI
    @15
    cW
    mptexg
    syl
    @190
    wph
    vk
    cI
    @15
    funmpt
    a1i
    wph
    cP
    cur
    fvexd
    @44
    @188
    @4
    @16
    cvv
    cvv
    @62
    suppssfifsupp
    syl32anc
    gsumzres
    3eqtr2d
    eqtrd
end
