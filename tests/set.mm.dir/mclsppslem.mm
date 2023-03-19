include "cv.mm"
include "cfv.mm"
include "ccnv.mm"
include "co.mm"
include "cima.mm"
include "wcel.mm"
include "crn.mm"
include "wf.mm"
include "msubf.mm"
include "syl.mm"
include "wss.mm"
include "wceq.mm"
include "wa.mm"
include "cfn.mm"
include "cotp.mm"
include "cmpst.mm"
include "w3a.mm"
include "cmax.mm"
include "cmsta.mm"
include "cmfs.mm"
include "eqid.mm"
include "maxsta.mm"
include "mstapst.mm"
include "syl6ss.mm"
include "sseldd.mm"
include "elmpst.mm"
include "sylib.mm"
include "simp3d.mm"
include "ffvelrnd.mm"
include "ccom.mm"
include "fvco3.mm"
include "syl2anc.mm"
include "msubco.mm"
include "wfn.mm"
include "fco.mm"
include "ffn.mm"
include "adantr.mm"
include "cun.mm"
include "wfun.mm"
include "cdm.mm"
include "wb.mm"
include "ffun.mm"
include "simp2bi.mm"
include "simpld.mm"
include "mvhf.mm"
include "frn.mm"
include "3syl.mm"
include "unssd.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "mpbid.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "eqtri.mm"
include "syl6sseqr.mm"
include "unssad.mm"
include "sselda.mm"
include "elpreima.mm"
include "simplbda.mm"
include "unssbd.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "wbr.mm"
include "wrex.mm"
include "ciun.mm"
include "cxp.mm"
include "simp1d.mm"
include "cid.mm"
include "cdif.mm"
include "mdvval.mm"
include "difss.mm"
include "eqsstri.mm"
include "ssbrd.mm"
include "imp.mm"
include "brxp.mm"
include "fveq2d.mm"
include "msubvrs.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "eliun.mm"
include "syl6bb.mm"
include "simprd.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "wi.mm"
include "simpll.mm"
include "wal.mm"
include "cvv.mm"
include "vex.mm"
include "breq12.mm"
include "simpl.mm"
include "simpr.mm"
include "xpeq12d.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "spc2gv.mm"
include "mp2an.mm"
include "syl5bir.mm"
include "3anbi123d.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "vtocl2.mm"
include "3exp2.mm"
include "imp4b.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "exp4b.mm"
include "3imp2.mm"
include "mclsax.mm"
include "eqeltrrd.mm"
include "mpbir2and.mm"

theorem mclsppslem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let cT: class T
  let vm: setvar m
  let vo: setvar o
  let cE: class E
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vu: setvar u
  let vc: setvar c
  let vd: setvar d
  assume mclspps.d: |- D = ( mDV ` T )
  assume mclspps.e: |- E = ( mEx ` T )
  assume mclspps.c: |- C = ( mCls ` T )
  assume mclspps.1: |- ( ph -> T e. mFS )
  assume mclspps.2: |- ( ph -> K C_ D )
  assume mclspps.3: |- ( ph -> B C_ E )
  assume mclspps.j: |- J = ( mPPSt ` T )
  assume mclspps.l: |- L = ( mSubst ` T )
  assume mclspps.v: |- V = ( mVR ` T )
  assume mclspps.h: |- H = ( mVH ` T )
  assume mclspps.w: |- W = ( mVars ` T )
  assume mclspps.4: |- ( ph -> <. M , O , P >. e. J )
  assume mclspps.5: |- ( ph -> S e. ran L )
  assume mclspps.6: |- ( ( ph /\ x e. O ) -> ( S ` x ) e. ( K C B ) )
  assume mclspps.7: |- ( ( ph /\ v e. V ) -> ( S ` ( H ` v ) ) e. ( K C B ) )
  assume mclspps.8: |- ( ( ph /\ ( x M y /\ a e. ( W ` ( S ` ( H ` x ) ) ) /\ b e. ( W ` ( S ` ( H ` y ) ) ) ) ) -> a K b )
  assume mclsppslem.9: |- ( ph -> <. m , o , p >. e. ( mAx ` T ) )
  assume mclsppslem.10: |- ( ph -> s e. ran L )
  assume mclsppslem.11: |- ( ph -> ( s " ( o u. ran H ) ) C_ ( `' S " ( K C B ) ) )
  assume mclsppslem.12: |- ( ph -> A. z A. w ( z m w -> ( ( W ` ( s ` ( H ` z ) ) ) X. ( W ` ( s ` ( H ` w ) ) ) ) C_ M ) )

  disjoint m o
  disjoint m p
  disjoint m s
  disjoint m v
  disjoint E m
  disjoint o p
  disjoint o s
  disjoint o v
  disjoint E o
  disjoint p s
  disjoint p v
  disjoint E p
  disjoint s v
  disjoint E s
  disjoint E v
  disjoint a b
  disjoint a m
  disjoint a o
  disjoint a p
  disjoint a s
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint H a
  disjoint b m
  disjoint b o
  disjoint b p
  disjoint b s
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint H b
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint H m
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint H o
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint H p
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint H s
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint H v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint H w
  disjoint x y
  disjoint x z
  disjoint H x
  disjoint y z
  disjoint H y
  disjoint H z
  disjoint V v
  disjoint V z
  disjoint K a
  disjoint K b
  disjoint K m
  disjoint K o
  disjoint K p
  disjoint K s
  disjoint K v
  disjoint K x
  disjoint K y
  disjoint T a
  disjoint T b
  disjoint T m
  disjoint T o
  disjoint T p
  disjoint T s
  disjoint T v
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint L a
  disjoint L b
  disjoint L m
  disjoint L o
  disjoint L p
  disjoint L s
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint S a
  disjoint S b
  disjoint S m
  disjoint S o
  disjoint S p
  disjoint S s
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint B a
  disjoint B b
  disjoint B m
  disjoint B o
  disjoint B p
  disjoint B s
  disjoint B v
  disjoint B x
  disjoint B y
  disjoint W a
  disjoint W b
  disjoint W m
  disjoint W o
  disjoint W p
  disjoint W s
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint C a
  disjoint C b
  disjoint C m
  disjoint C o
  disjoint C p
  disjoint C s
  disjoint C v
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint M a
  disjoint M b
  disjoint M m
  disjoint M o
  disjoint M p
  disjoint M s
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint O m
  disjoint O o
  disjoint O p
  disjoint O s
  disjoint O v
  disjoint O w
  disjoint O x
  disjoint O z
  disjoint a ph
  disjoint b ph
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint m t
  disjoint m u
  disjoint o t
  disjoint o u
  disjoint p t
  disjoint p u
  disjoint s t
  disjoint s u
  disjoint t u
  disjoint t v
  disjoint E t
  disjoint u v
  disjoint E u
  disjoint a c
  disjoint a t
  disjoint a u
  disjoint b c
  disjoint b t
  disjoint b u
  disjoint c m
  disjoint c o
  disjoint c p
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint H c
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint H t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint H u
  disjoint V c
  disjoint V t
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint K c
  disjoint d m
  disjoint d o
  disjoint d p
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint K d
  disjoint K t
  disjoint K u
  disjoint T c
  disjoint d w
  disjoint d z
  disjoint T d
  disjoint T u
  disjoint L c
  disjoint L d
  disjoint S c
  disjoint S d
  disjoint S t
  disjoint S u
  disjoint B c
  disjoint B d
  disjoint B t
  disjoint W c
  disjoint W u
  disjoint C c
  disjoint C t
  disjoint c ph
  disjoint d ph
  disjoint ph t
  disjoint ph u
  assert |- ( ph -> ( s ` p ) e. ( `' S " ( K C B ) ) )

  proof
    wph
    vp
    cv
    #
    vs
    cv
    #
    cfv
    #
    cS
    ccnv
    #
    cK
    cB
    cC
    co
    #
    cima
    #
    wcel
    #
    @2
    cE
    wcel
    #
    @2
    cS
    cfv
    #
    @4
    wcel
    #
    wph
    cE
    cE
    @0
    @1
    wph
    @1
    cL
    crn
    #
    wcel
    #
    cE
    cE
    @1
    wf
    #
    mclsppslem.10
    cL
    cT
    cE
    @1
    mclspps.l
    mclspps.e
    msubf
    syl
    #
    wph
    vm
    cv
    #
    cD
    wss
    #
    @14
    ccnv
    @14
    wceq
    #
    wa
    #
    vo
    cv
    #
    cE
    wss
    #
    @18
    cfn
    wcel
    #
    wa
    #
    @0
    cE
    wcel
    #
    wph
    @14
    @18
    @0
    cotp
    #
    cT
    cmpst
    cfv
    #
    wcel
    #
    @17
    @21
    @22
    w3a
    wph
    cT
    cmax
    cfv
    #
    @24
    @23
    wph
    @26
    cT
    cmsta
    cfv
    #
    @24
    wph
    cT
    cmfs
    wcel
    #
    @26
    @27
    wss
    mclspps.1
    @26
    @27
    cT
    @26
    eqid
    #
    @27
    eqid
    #
    maxsta
    syl
    @24
    @27
    cT
    @24
    eqid
    #
    @30
    mstapst
    syl6ss
    mclsppslem.9
    sseldd
    #
    @0
    @14
    @24
    cT
    cE
    @18
    cD
    mclspps.d
    mclspps.e
    @31
    elmpst
    #
    sylib
    #
    simp3d
    #
    ffvelrnd
    wph
    @0
    cS
    @1
    ccom
    #
    cfv
    #
    @8
    @4
    wph
    @12
    @22
    @37
    @8
    wceq
    @13
    @35
    cE
    cE
    @0
    cS
    @1
    fvco3
    syl2anc
    wph
    vc
    vd
    vt
    @26
    cB
    cC
    cD
    @0
    @36
    cT
    cE
    cH
    cK
    cL
    @14
    @18
    cV
    cW
    va
    vb
    mclspps.d
    mclspps.e
    mclspps.c
    mclspps.1
    mclspps.2
    mclspps.3
    @29
    mclspps.l
    mclspps.v
    mclspps.h
    mclspps.w
    mclsppslem.9
    wph
    cS
    @10
    wcel
    #
    @11
    @36
    @10
    wcel
    mclspps.5
    mclsppslem.10
    cL
    cT
    cS
    @1
    mclspps.l
    msubco
    syl2anc
    wph
    vc
    cv
    #
    @18
    wcel
    #
    wa
    @36
    cE
    wfn
    #
    @39
    @36
    ccnv
    #
    @4
    cima
    #
    wcel
    #
    @39
    @36
    cfv
    @4
    wcel
    #
    wph
    @41
    @40
    wph
    cE
    cE
    @36
    wf
    #
    @41
    wph
    cE
    cE
    cS
    wf
    #
    @12
    @46
    wph
    @38
    @47
    mclspps.5
    cL
    cT
    cE
    cS
    mclspps.l
    mclspps.e
    msubf
    syl
    #
    @13
    cE
    cE
    cE
    cS
    @1
    fco
    syl2anc
    cE
    cE
    @36
    ffn
    syl
    #
    adantr
    wph
    @18
    @43
    @39
    wph
    @18
    cH
    crn
    #
    @43
    wph
    @18
    @50
    cun
    #
    @1
    ccnv
    #
    @5
    cima
    #
    @43
    wph
    @1
    @51
    cima
    @5
    wss
    #
    @51
    @53
    wss
    #
    mclsppslem.11
    wph
    @1
    wfun
    #
    @51
    @1
    cdm
    #
    wss
    @54
    @55
    wb
    wph
    @12
    @56
    @13
    cE
    cE
    @1
    ffun
    syl
    wph
    @51
    cE
    @57
    wph
    @18
    @50
    cE
    wph
    @19
    @20
    wph
    @25
    @21
    @32
    @25
    @17
    @21
    @22
    @33
    simp2bi
    syl
    simpld
    wph
    @28
    cV
    cE
    cH
    wf
    #
    @50
    cE
    wss
    mclspps.1
    cT
    cE
    cH
    cV
    mclspps.v
    mclspps.e
    mclspps.h
    mvhf
    #
    cV
    cE
    cH
    frn
    3syl
    unssd
    wph
    @12
    @57
    cE
    wceq
    @13
    cE
    cE
    @1
    fdm
    syl
    sseqtr4d
    @51
    @5
    @1
    funimass3
    syl2anc
    mpbid
    @43
    @52
    @3
    ccom
    #
    @4
    cima
    @53
    @42
    @60
    @4
    cS
    @1
    cnvco
    imaeq1i
    @52
    @3
    @4
    imaco
    eqtri
    syl6sseqr
    #
    unssad
    sselda
    @41
    @44
    @39
    cE
    wcel
    @45
    cE
    @39
    @4
    @36
    elpreima
    simplbda
    syl2anc
    wph
    vt
    cv
    #
    cV
    wcel
    #
    wa
    #
    @41
    @62
    cH
    cfv
    #
    @43
    wcel
    #
    @65
    @36
    cfv
    @4
    wcel
    #
    wph
    @41
    @63
    @49
    adantr
    @64
    @50
    @43
    @65
    wph
    @50
    @43
    wss
    @63
    wph
    @18
    @50
    @43
    @61
    unssbd
    adantr
    wph
    cH
    cV
    wfn
    #
    @63
    @65
    @50
    wcel
    wph
    @28
    @58
    @68
    mclspps.1
    @59
    cV
    cE
    cH
    ffn
    3syl
    cV
    @62
    cH
    fnfvelrn
    sylan
    sseldd
    @41
    @66
    @65
    cE
    wcel
    @67
    cE
    @65
    @4
    @36
    elpreima
    simplbda
    syl2anc
    wph
    @39
    vd
    cv
    #
    @14
    wbr
    #
    va
    cv
    #
    @39
    cH
    cfv
    #
    @36
    cfv
    #
    cW
    cfv
    #
    wcel
    #
    vb
    cv
    #
    @69
    cH
    cfv
    #
    @36
    cfv
    #
    cW
    cfv
    #
    wcel
    #
    @71
    @76
    cK
    wbr
    #
    wph
    @70
    @75
    @80
    @81
    wph
    @70
    wa
    #
    @75
    @80
    wa
    @71
    vu
    cv
    #
    cH
    cfv
    #
    cS
    cfv
    #
    cW
    cfv
    #
    wcel
    #
    vu
    @72
    @1
    cfv
    #
    cW
    cfv
    #
    wrex
    #
    @76
    vv
    cv
    #
    cH
    cfv
    #
    cS
    cfv
    #
    cW
    cfv
    #
    wcel
    #
    vv
    @77
    @1
    cfv
    #
    cW
    cfv
    #
    wrex
    #
    wa
    #
    @81
    @82
    @75
    @90
    @80
    @98
    @82
    @75
    @71
    vu
    @89
    @86
    ciun
    #
    wcel
    @90
    @82
    @74
    @100
    @71
    @82
    @74
    @88
    cS
    cfv
    #
    cW
    cfv
    #
    @100
    @82
    @73
    @101
    cW
    @82
    @12
    @72
    cE
    wcel
    @73
    @101
    wceq
    wph
    @12
    @70
    @13
    adantr
    #
    @82
    cV
    cE
    @39
    cH
    wph
    @58
    @70
    wph
    @28
    @58
    mclspps.1
    @59
    syl
    adantr
    #
    @82
    @39
    cV
    wcel
    #
    @69
    cV
    wcel
    #
    @82
    @39
    @69
    cV
    cV
    cxp
    #
    wbr
    #
    @105
    @106
    wa
    wph
    @70
    @108
    wph
    @14
    @107
    @39
    @69
    wph
    @14
    cD
    @107
    wph
    @15
    @16
    wph
    @17
    @21
    @22
    @34
    simp1d
    simpld
    cD
    @107
    cid
    cdif
    @107
    cD
    cT
    cV
    mclspps.v
    mclspps.d
    mdvval
    @107
    cid
    difss
    eqsstri
    syl6ss
    ssbrd
    imp
    @39
    @69
    cV
    cV
    brxp
    sylib
    #
    simpld
    ffvelrnd
    #
    cE
    cE
    @72
    cS
    @1
    fvco3
    syl2anc
    fveq2d
    @82
    @28
    @38
    @88
    cE
    wcel
    @102
    @100
    wceq
    wph
    @28
    @70
    mclspps.1
    adantr
    #
    wph
    @38
    @70
    mclspps.5
    adantr
    #
    @82
    cE
    cE
    @72
    @1
    @103
    @110
    ffvelrnd
    vu
    cL
    cT
    cE
    cS
    cH
    cW
    @88
    mclspps.l
    mclspps.e
    mclspps.w
    mclspps.h
    msubvrs
    syl3anc
    eqtrd
    eleq2d
    vu
    @71
    @89
    @86
    eliun
    syl6bb
    @82
    @80
    @76
    vv
    @97
    @94
    ciun
    #
    wcel
    @98
    @82
    @79
    @113
    @76
    @82
    @79
    @96
    cS
    cfv
    #
    cW
    cfv
    #
    @113
    @82
    @78
    @114
    cW
    @82
    @12
    @77
    cE
    wcel
    @78
    @114
    wceq
    @103
    @82
    cV
    cE
    @69
    cH
    @104
    @82
    @105
    @106
    @109
    simprd
    ffvelrnd
    #
    cE
    cE
    @77
    cS
    @1
    fvco3
    syl2anc
    fveq2d
    @82
    @28
    @38
    @96
    cE
    wcel
    @115
    @113
    wceq
    @111
    @112
    @82
    cE
    cE
    @77
    @1
    @103
    @116
    ffvelrnd
    vv
    cL
    cT
    cE
    cS
    cH
    cW
    @96
    mclspps.l
    mclspps.e
    mclspps.w
    mclspps.h
    msubvrs
    syl3anc
    eqtrd
    eleq2d
    vv
    @76
    @97
    @94
    eliun
    syl6bb
    anbi12d
    @99
    @87
    @95
    wa
    #
    vv
    @97
    wrex
    vu
    @89
    wrex
    @82
    @81
    @87
    @95
    vu
    vv
    @89
    @97
    reeanv
    @82
    @117
    @81
    vu
    vv
    @89
    @97
    @82
    @83
    @89
    wcel
    @91
    @97
    wcel
    wa
    #
    wa
    wph
    @83
    @91
    cM
    wbr
    #
    @117
    @81
    wi
    wph
    @70
    @118
    simpll
    @82
    @118
    @119
    @118
    @83
    @91
    @89
    @97
    cxp
    #
    wbr
    @82
    @119
    @83
    @91
    @89
    @97
    brxp
    @82
    @120
    cM
    @83
    @91
    wph
    @70
    @120
    cM
    wss
    #
    wph
    vz
    cv
    #
    vw
    cv
    #
    @14
    wbr
    #
    @122
    cH
    cfv
    #
    @1
    cfv
    #
    cW
    cfv
    #
    @123
    cH
    cfv
    #
    @1
    cfv
    #
    cW
    cfv
    #
    cxp
    #
    cM
    wss
    #
    wi
    #
    vw
    wal
    vz
    wal
    #
    @70
    @121
    wi
    #
    mclsppslem.12
    @39
    cvv
    wcel
    @69
    cvv
    wcel
    @134
    @135
    wi
    vc
    vex
    vd
    vex
    @133
    @135
    vz
    vw
    @39
    @69
    cvv
    cvv
    @122
    @39
    wceq
    #
    @123
    @69
    wceq
    #
    wa
    #
    @124
    @70
    @132
    @121
    @122
    @39
    @123
    @69
    @14
    breq12
    @138
    @131
    @120
    cM
    @138
    @127
    @89
    @130
    @97
    @138
    @126
    @88
    cW
    @138
    @125
    @72
    @1
    @138
    @122
    @39
    cH
    @136
    @137
    simpl
    fveq2d
    fveq2d
    fveq2d
    @138
    @129
    @96
    cW
    @138
    @128
    @77
    @1
    @138
    @123
    @69
    cH
    @136
    @137
    simpr
    fveq2d
    fveq2d
    fveq2d
    xpeq12d
    sseq1d
    imbi12d
    spc2gv
    mp2an
    syl
    imp
    ssbrd
    syl5bir
    imp
    wph
    @119
    @87
    @95
    @81
    wph
    @119
    @87
    @95
    @81
    wph
    vx
    cv
    #
    vy
    cv
    #
    cM
    wbr
    #
    @71
    @139
    cH
    cfv
    #
    cS
    cfv
    #
    cW
    cfv
    #
    wcel
    #
    @76
    @140
    cH
    cfv
    #
    cS
    cfv
    #
    cW
    cfv
    #
    wcel
    #
    w3a
    #
    wa
    #
    @81
    wi
    wph
    @119
    @87
    @95
    w3a
    #
    wa
    #
    @81
    wi
    vx
    vy
    @83
    @91
    vu
    vex
    vv
    vex
    @139
    @83
    wceq
    #
    @140
    @91
    wceq
    #
    wa
    #
    @151
    @153
    @81
    @156
    @150
    @152
    wph
    @156
    @141
    @119
    @145
    @87
    @149
    @95
    @139
    @83
    @140
    @91
    cM
    breq12
    @156
    @144
    @86
    @71
    @156
    @143
    @85
    cW
    @156
    @142
    @84
    cS
    @156
    @139
    @83
    cH
    @154
    @155
    simpl
    fveq2d
    fveq2d
    fveq2d
    eleq2d
    @156
    @148
    @94
    @76
    @156
    @147
    @93
    cW
    @156
    @146
    @92
    cS
    @156
    @140
    @91
    cH
    @154
    @155
    simpr
    fveq2d
    fveq2d
    fveq2d
    eleq2d
    3anbi123d
    anbi2d
    imbi1d
    mclspps.8
    vtocl2
    3exp2
    imp4b
    syl2anc
    rexlimdvva
    syl5bir
    sylbid
    exp4b
    3imp2
    mclsax
    eqeltrrd
    wph
    cS
    cE
    wfn
    #
    @6
    @7
    @9
    wa
    wb
    wph
    @47
    @157
    @48
    cE
    cE
    cS
    ffn
    syl
    cE
    @2
    @4
    cS
    elpreima
    syl
    mpbir2and
end
