include "wf1o.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt2.mm"
include "czrh.mm"
include "cpsgn.mm"
include "ccom.mm"
include "wceq.mm"
include "csymg.mm"
include "cplusg.mm"
include "c0g.mm"
include "cbs.mm"
include "cpmtr.mm"
include "crn.mm"
include "weq.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpt2eq3dv.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "eqid.mm"
include "cfn.mm"
include "cgrp.mm"
include "cmnd.mm"
include "3ad2ant1.mm"
include "symggrp.mm"
include "grpmnd.mm"
include "3syl.mm"
include "wss.mm"
include "symgtrf.mm"
include "a1i.mm"
include "csubmnd.mm"
include "cmrc.mm"
include "symggen2.mm"
include "syl.mm"
include "eqcomd.mm"
include "crg.mm"
include "wf.mm"
include "simp3.mm"
include "ffvelrnd.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "cmgp.mm"
include "cmhm.mm"
include "zrhpsgnmhm.mm"
include "ringidval.mm"
include "mhm0.mm"
include "cid.mm"
include "cres.mm"
include "symgid.mm"
include "fveq1d.mm"
include "simp2.mm"
include "fvresi.mm"
include "eqtr3d.mm"
include "mpt2eq3dva.mm"
include "cxp.mm"
include "wfn.mm"
include "cmap.mm"
include "matbas2i.mm"
include "3ad2ant3.mm"
include "elmapi.mm"
include "ffn.mm"
include "fnov.mm"
include "sylib.mm"
include "eqtr4d.mm"
include "3eqtr4rd.mm"
include "wa.mm"
include "cminusg.mm"
include "sseli.mm"
include "symgov.mm"
include "symgbasf1o.mm"
include "f1of.mm"
include "fvco3.mm"
include "eqtrd.mm"
include "symgbasf.mm"
include "wne.mm"
include "cpr.mm"
include "wrex.mm"
include "pmtrrn2.mm"
include "wi.mm"
include "cif.mm"
include "simpll1.mm"
include "df-3an.mm"
include "biimpri.mm"
include "adantl.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "simpllr.mm"
include "simprlr.mm"
include "simpr.mm"
include "fovrnd.mm"
include "simprll.mm"
include "jca.mm"
include "simp1lr.mm"
include "mdetunilem6.mm"
include "simpl1.mm"
include "simprr.mm"
include "pmtrprfv.mm"
include "syl13anc.mm"
include "sylan9eqr.mm"
include "iftrue.mm"
include "wn.mm"
include "prcom.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "simplrl.mm"
include "simprd.mm"
include "simpld.mm"
include "simplrr.mm"
include "necomd.mm"
include "syl5eq.mm"
include "adantlr.mm"
include "cdif.mm"
include "cdm.mm"
include "wo.mm"
include "vex.mm"
include "elpr.mm"
include "notbii.mm"
include "ioran.mm"
include "sylbbr.mm"
include "adantll.mm"
include "wb.mm"
include "c2o.mm"
include "cen.mm"
include "wbr.mm"
include "prssi.mm"
include "pr2ne.mm"
include "mpbird.mm"
include "pmtrmvd.mm"
include "syl3anc.mm"
include "eleq2d.mm"
include "notbid.mm"
include "pmtrf.mm"
include "fnelnfp.mm"
include "necon2bbid.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "3adant3.mm"
include "sylan.mm"
include "pm2.61i.mm"
include "mpt2eq3ia.mm"
include "3eqtr4d.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "expr.mm"
include "impd.mm"
include "rexlimdvva.mm"
include "syl5.mm"
include "3impia.mm"
include "syl3an2.mm"
include "mgpbas.mm"
include "mhmf.mm"
include "simp13.mm"
include "ringmneg1.mm"
include "mgpplusg.mm"
include "mhmlin.mm"
include "cevpm.mm"
include "pmtrodpm.mm"
include "zrhpsgnodpm.mm"
include "oveq2d.mm"
include "rngnegr.mm"
include "3eqtrrd.mm"
include "3eqtrd.mm"
include "elsymgbas.mm"
include "mrcmndind.mm"

theorem mdetunilem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cE: class E
  let cF: class F
  let cK: class K
  let cN: class N
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cY: class Y
  let cG: class G
  let cH: class H
  assume mdetuni.a: |- A = ( N Mat R )
  assume mdetuni.b: |- B = ( Base ` A )
  assume mdetuni.k: |- K = ( Base ` R )
  assume mdetuni.0g: |- .0. = ( 0g ` R )
  assume mdetuni.1r: |- .1. = ( 1r ` R )
  assume mdetuni.pg: |- .+ = ( +g ` R )
  assume mdetuni.tg: |- .x. = ( .r ` R )
  assume mdetuni.n: |- ( ph -> N e. Fin )
  assume mdetuni.r: |- ( ph -> R e. Ring )
  assume mdetuni.ff: |- ( ph -> D : B --> K )
  assume mdetuni.al: |- ( ph -> A. x e. B A. y e. N A. z e. N ( ( y =/= z /\ A. w e. N ( y x w ) = ( z x w ) ) -> ( D ` x ) = .0. ) )
  assume mdetuni.li: |- ( ph -> A. x e. B A. y e. B A. z e. B A. w e. N ( ( ( x |` ( { w } X. N ) ) = ( ( y |` ( { w } X. N ) ) oF .+ ( z |` ( { w } X. N ) ) ) /\ ( x |` ( ( N \ { w } ) X. N ) ) = ( y |` ( ( N \ { w } ) X. N ) ) /\ ( x |` ( ( N \ { w } ) X. N ) ) = ( z |` ( ( N \ { w } ) X. N ) ) ) -> ( D ` x ) = ( ( D ` y ) .+ ( D ` z ) ) ) )
  assume mdetuni.sc: |- ( ph -> A. x e. B A. y e. K A. z e. B A. w e. N ( ( ( x |` ( { w } X. N ) ) = ( ( ( { w } X. N ) X. { y } ) oF .x. ( z |` ( { w } X. N ) ) ) /\ ( x |` ( ( N \ { w } ) X. N ) ) = ( z |` ( ( N \ { w } ) X. N ) ) ) -> ( D ` x ) = ( y .x. ( D ` z ) ) ) )

  disjoint E a
  disjoint E b
  disjoint a b
  disjoint F a
  disjoint F b
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ph w
  disjoint a ph
  disjoint b ph
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint a x
  disjoint b x
  disjoint y z
  disjoint w y
  disjoint a y
  disjoint b y
  disjoint w z
  disjoint a z
  disjoint b z
  disjoint a w
  disjoint b w
  disjoint a b
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint B a
  disjoint B b
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint K w
  disjoint K a
  disjoint K b
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N w
  disjoint N a
  disjoint N b
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint D a
  disjoint D b
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .x. w
  disjoint .+ a
  disjoint .+ b
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .+ w
  disjoint .0. a
  disjoint .0. b
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  disjoint .0. w
  disjoint .1. a
  disjoint .1. b
  disjoint .1. x
  disjoint .1. y
  disjoint .1. z
  disjoint .1. w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint A a
  disjoint A b
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint E w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F w
  disjoint E c
  disjoint E d
  disjoint E e
  disjoint E f
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint d e
  disjoint d f
  disjoint e f
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint R c
  disjoint R d
  disjoint R f
  disjoint .x. c
  disjoint .x. d
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint c x
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint c z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint c w
  disjoint d w
  disjoint e w
  disjoint f w
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint d e
  disjoint d f
  disjoint e f
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint K c
  disjoint K d
  disjoint K e
  disjoint K f
  disjoint N c
  disjoint N d
  disjoint N e
  disjoint N f
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y e
  disjoint Y f
  disjoint .x. e
  disjoint .+ e
  disjoint .0. c
  disjoint .0. d
  disjoint .0. e
  disjoint .1. c
  disjoint .1. d
  disjoint .1. e
  disjoint R e
  disjoint A c
  disjoint A d
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint G w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint H w
  assert |- ( ( ph /\ E : N -1-1-onto-> N /\ F e. B ) -> ( D ` ( a e. N , b e. N |-> ( ( E ` a ) F b ) ) ) = ( ( ( ( ZRHom ` R ) o. ( pmSgn ` N ) ) ` E ) .x. ( D ` F ) ) )

  proof
    wph
    cN
    cN
    cE
    wf1o
    #
    cF
    cB
    wcel
    #
    w3a
    #
    va
    vb
    cN
    cN
    va
    cv
    #
    vc
    cv
    #
    cfv
    #
    vb
    cv
    #
    cF
    co
    #
    cmpt2
    #
    cD
    cfv
    #
    @4
    cR
    czrh
    cfv
    #
    cN
    cpsgn
    cfv
    #
    ccom
    #
    cfv
    #
    cF
    cD
    cfv
    #
    c.x
    co
    #
    wceq
    va
    vb
    cN
    cN
    @3
    vd
    cv
    #
    cfv
    #
    @6
    cF
    co
    #
    cmpt2
    #
    cD
    cfv
    #
    @16
    @12
    cfv
    #
    @14
    c.x
    co
    #
    wceq
    #
    va
    vb
    cN
    cN
    @3
    @16
    ve
    cv
    #
    cN
    csymg
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cfv
    #
    @6
    cF
    co
    #
    cmpt2
    #
    cD
    cfv
    #
    @27
    @12
    cfv
    #
    @14
    c.x
    co
    #
    wceq
    va
    vb
    cN
    cN
    @3
    @25
    c0g
    cfv
    #
    cfv
    #
    @6
    cF
    co
    #
    cmpt2
    #
    cD
    cfv
    #
    @34
    @12
    cfv
    #
    @14
    c.x
    co
    #
    wceq
    va
    vb
    cN
    cN
    @3
    cE
    cfv
    #
    @6
    cF
    co
    #
    cmpt2
    #
    cD
    cfv
    #
    cE
    @12
    cfv
    #
    @14
    c.x
    co
    #
    wceq
    vc
    vd
    ve
    cE
    @25
    cbs
    cfv
    #
    @26
    cN
    cpmtr
    cfv
    #
    crn
    #
    @25
    @34
    vc
    vd
    weq
    #
    @9
    @20
    @15
    @22
    @50
    @8
    @19
    cD
    @50
    va
    vb
    cN
    cN
    @7
    @18
    @50
    @5
    @17
    @6
    cF
    @3
    @4
    @16
    fveq1
    oveq1d
    mpt2eq3dv
    fveq2d
    @50
    @13
    @21
    @14
    c.x
    @4
    @16
    @12
    fveq2
    oveq1d
    eqeq12d
    @4
    @27
    wceq
    #
    @9
    @31
    @15
    @33
    @51
    @8
    @30
    cD
    @51
    va
    vb
    cN
    cN
    @7
    @29
    @51
    @5
    @28
    @6
    cF
    @3
    @4
    @27
    fveq1
    oveq1d
    mpt2eq3dv
    fveq2d
    @51
    @13
    @32
    @14
    c.x
    @4
    @27
    @12
    fveq2
    oveq1d
    eqeq12d
    @4
    @34
    wceq
    #
    @9
    @38
    @15
    @40
    @52
    @8
    @37
    cD
    @52
    va
    vb
    cN
    cN
    @7
    @36
    @52
    @5
    @35
    @6
    cF
    @3
    @4
    @34
    fveq1
    oveq1d
    mpt2eq3dv
    fveq2d
    @52
    @13
    @39
    @14
    c.x
    @4
    @34
    @12
    fveq2
    oveq1d
    eqeq12d
    @4
    cE
    wceq
    #
    @9
    @44
    @15
    @46
    @53
    @8
    @43
    cD
    @53
    va
    vb
    cN
    cN
    @7
    @42
    @53
    @5
    @41
    @6
    cF
    @3
    @4
    cE
    fveq1
    oveq1d
    mpt2eq3dv
    fveq2d
    @53
    @13
    @45
    @14
    c.x
    @4
    cE
    @12
    fveq2
    oveq1d
    eqeq12d
    @34
    eqid
    #
    @26
    eqid
    #
    @47
    eqid
    #
    @2
    cN
    cfn
    wcel
    #
    @25
    cgrp
    wcel
    @25
    cmnd
    wcel
    wph
    @0
    @57
    @1
    mdetuni.n
    3ad2ant1
    #
    cN
    @25
    cfn
    @25
    eqid
    #
    symggrp
    @25
    grpmnd
    3syl
    @49
    @47
    wss
    @2
    @47
    cN
    @49
    @25
    @49
    eqid
    #
    @59
    @56
    symgtrf
    #
    a1i
    wph
    @0
    @47
    @49
    @25
    csubmnd
    cfv
    cmrc
    cfv
    #
    cfv
    #
    wceq
    @1
    wph
    @63
    @47
    wph
    @57
    @63
    @47
    wceq
    mdetuni.n
    @47
    cN
    @49
    @25
    @62
    @60
    @59
    @56
    @62
    eqid
    symggen2
    syl
    eqcomd
    3ad2ant1
    @2
    c.1
    @14
    c.x
    co
    #
    @14
    @40
    @38
    @2
    cR
    crg
    wcel
    #
    @14
    cK
    wcel
    @64
    @14
    wceq
    wph
    @0
    @65
    @1
    mdetuni.r
    3ad2ant1
    #
    @2
    cB
    cK
    cF
    cD
    wph
    @0
    cB
    cK
    cD
    wf
    #
    @1
    mdetuni.ff
    3ad2ant1
    #
    wph
    @0
    @1
    simp3
    ffvelrnd
    cK
    cR
    c.x
    c.1
    @14
    mdetuni.k
    mdetuni.tg
    mdetuni.1r
    ringlidm
    syl2anc
    @2
    @39
    c.1
    @14
    c.x
    wph
    @0
    @39
    c.1
    wceq
    #
    @1
    wph
    @12
    @25
    cR
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    @69
    wph
    @65
    @57
    @71
    mdetuni.r
    mdetuni.n
    cN
    cR
    zrhpsgnmhm
    syl2anc
    #
    @25
    @70
    @12
    c.1
    @34
    @54
    cR
    c.1
    @70
    @70
    eqid
    #
    mdetuni.1r
    ringidval
    mhm0
    syl
    3ad2ant1
    oveq1d
    @2
    @37
    cF
    cD
    @2
    @37
    va
    vb
    cN
    cN
    @3
    @6
    cF
    co
    #
    cmpt2
    #
    cF
    @2
    va
    vb
    cN
    cN
    @36
    @74
    @2
    @3
    cN
    wcel
    #
    @6
    cN
    wcel
    #
    w3a
    #
    @35
    @3
    @6
    cF
    @78
    @3
    cid
    cN
    cres
    #
    cfv
    #
    @35
    @3
    @78
    @3
    @79
    @34
    @2
    @76
    @79
    @34
    wceq
    #
    @77
    wph
    @0
    @81
    @1
    wph
    @57
    @81
    mdetuni.n
    cN
    @25
    cfn
    @59
    symgid
    syl
    3ad2ant1
    3ad2ant1
    fveq1d
    @78
    @76
    @80
    @3
    wceq
    @2
    @76
    @77
    simp2
    cN
    @3
    fvresi
    syl
    eqtr3d
    oveq1d
    mpt2eq3dva
    @2
    cF
    cN
    cN
    cxp
    #
    wfn
    #
    cF
    @75
    wceq
    @2
    cF
    cK
    @82
    cmap
    co
    wcel
    #
    @82
    cK
    cF
    wf
    #
    @83
    @1
    wph
    @84
    @0
    cA
    cB
    cR
    cK
    cF
    cN
    mdetuni.a
    mdetuni.k
    mdetuni.b
    matbas2i
    3ad2ant3
    #
    cF
    cK
    @82
    elmapi
    #
    @82
    cK
    cF
    ffn
    3syl
    va
    vb
    cN
    cN
    cF
    fnov
    sylib
    eqtr4d
    fveq2d
    3eqtr4rd
    @2
    @16
    @47
    wcel
    #
    @24
    @49
    wcel
    #
    w3a
    #
    @23
    wa
    @31
    @20
    cR
    cminusg
    cfv
    #
    cfv
    #
    @22
    @91
    cfv
    #
    @33
    @90
    @31
    @92
    wceq
    @23
    @90
    @31
    va
    vb
    cN
    cN
    @3
    @24
    cfv
    #
    @16
    cfv
    #
    @6
    cF
    co
    #
    cmpt2
    #
    cD
    cfv
    #
    @92
    @90
    @30
    @97
    cD
    @90
    va
    vb
    cN
    cN
    @29
    @96
    @90
    @76
    @77
    w3a
    #
    @28
    @95
    @6
    cF
    @99
    @28
    @3
    @16
    @24
    ccom
    #
    cfv
    #
    @95
    @90
    @76
    @28
    @101
    wceq
    @77
    @90
    @3
    @27
    @100
    @90
    @88
    @24
    @47
    wcel
    #
    @27
    @100
    wceq
    @2
    @88
    @89
    simp2
    #
    @89
    @2
    @102
    @88
    @49
    @47
    @24
    @61
    sseli
    3ad2ant3
    #
    cN
    @47
    @26
    @25
    @16
    @24
    @59
    @56
    @55
    symgov
    syl2anc
    fveq1d
    3ad2ant1
    @99
    cN
    cN
    @24
    wf
    #
    @76
    @101
    @95
    wceq
    @90
    @76
    @105
    @77
    @90
    @102
    cN
    cN
    @24
    wf1o
    @105
    @104
    cN
    @47
    @24
    @25
    @59
    @56
    symgbasf1o
    cN
    cN
    @24
    f1of
    3syl
    3ad2ant1
    @90
    @76
    @77
    simp2
    cN
    cN
    @3
    @16
    @24
    fvco3
    syl2anc
    eqtrd
    oveq1d
    mpt2eq3dva
    fveq2d
    @88
    @2
    cN
    cN
    @16
    wf
    #
    @89
    @98
    @92
    wceq
    #
    cN
    @47
    @16
    @25
    @59
    @56
    symgbasf
    @2
    @106
    @89
    @107
    @89
    @4
    vf
    cv
    #
    wne
    #
    @24
    @4
    @108
    cpr
    #
    @48
    cfv
    #
    wceq
    #
    wa
    #
    vf
    cN
    wrex
    vc
    cN
    wrex
    @2
    @106
    wa
    #
    @107
    vc
    vf
    cN
    @49
    @48
    @24
    @48
    eqid
    #
    @60
    pmtrrn2
    @114
    @113
    @107
    vc
    vf
    cN
    cN
    @114
    @4
    cN
    wcel
    #
    @108
    cN
    wcel
    #
    wa
    #
    wa
    @109
    @112
    @107
    @114
    @118
    @109
    @112
    @107
    wi
    @114
    @118
    @109
    wa
    #
    wa
    #
    @107
    @112
    va
    vb
    cN
    cN
    @3
    @111
    cfv
    #
    @16
    cfv
    #
    @6
    cF
    co
    #
    cmpt2
    #
    cD
    cfv
    #
    @92
    wceq
    @120
    va
    vb
    cN
    cN
    va
    vc
    weq
    #
    @108
    @16
    cfv
    #
    @6
    cF
    co
    #
    va
    vf
    weq
    #
    @4
    @16
    cfv
    #
    @6
    cF
    co
    #
    @18
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    va
    vb
    cN
    cN
    @126
    @131
    @129
    @128
    @18
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    @91
    cfv
    #
    @125
    @92
    wph
    @120
    vx
    vy
    vz
    vw
    cA
    cB
    cD
    c.pl
    cR
    c.x
    c.1
    @4
    @108
    @128
    @131
    @18
    cK
    cN
    c.0
    va
    vb
    mdetuni.a
    mdetuni.b
    mdetuni.k
    mdetuni.0g
    mdetuni.1r
    mdetuni.pg
    mdetuni.tg
    mdetuni.n
    mdetuni.r
    mdetuni.ff
    mdetuni.al
    mdetuni.li
    mdetuni.sc
    wph
    @0
    @1
    @106
    @119
    simpll1
    @119
    @116
    @117
    @109
    w3a
    #
    @114
    @140
    @119
    @116
    @117
    @109
    df-3an
    biimpri
    adantl
    @120
    @77
    wa
    #
    @128
    cK
    wcel
    @131
    cK
    wcel
    @141
    @127
    @6
    cK
    cN
    cN
    cF
    @114
    @85
    @119
    @77
    @2
    @85
    @106
    @2
    @84
    @85
    @86
    @87
    syl
    #
    adantr
    ad2antrr
    #
    @141
    cN
    cN
    @108
    @16
    @2
    @106
    @119
    @77
    simpllr
    #
    @120
    @117
    @77
    @114
    @116
    @117
    @109
    simprlr
    adantr
    ffvelrnd
    @120
    @77
    simpr
    #
    fovrnd
    @141
    @130
    @6
    cK
    cN
    cN
    cF
    @143
    @141
    cN
    cN
    @4
    @16
    @144
    @120
    @116
    @77
    @114
    @116
    @117
    @109
    simprll
    adantr
    ffvelrnd
    @145
    fovrnd
    jca
    @120
    @76
    @77
    w3a
    #
    @17
    @6
    cK
    cN
    cN
    cF
    @120
    @76
    @85
    @77
    @2
    @85
    @106
    @119
    @142
    ad2antrr
    3ad2ant1
    @146
    cN
    cN
    @3
    @16
    @2
    @106
    @119
    @76
    @77
    simp1lr
    @120
    @76
    @77
    simp2
    ffvelrnd
    @120
    @76
    @77
    simp3
    fovrnd
    mdetunilem6
    @120
    @124
    @134
    cD
    @114
    wph
    @119
    @124
    @134
    wceq
    wph
    @0
    @1
    @106
    simpl1
    wph
    @119
    wa
    #
    va
    vb
    cN
    cN
    @123
    @133
    @147
    @76
    @123
    @133
    wceq
    #
    @77
    @147
    @76
    wa
    #
    @126
    @148
    @149
    @126
    wa
    #
    @123
    @128
    @133
    @150
    @122
    @127
    @6
    cF
    @150
    @121
    @108
    @16
    @126
    @149
    @121
    @4
    @111
    cfv
    #
    @108
    @3
    @4
    @111
    fveq2
    @147
    @151
    @108
    wceq
    #
    @76
    @147
    @57
    @116
    @117
    @109
    @152
    wph
    @57
    @119
    mdetuni.n
    adantr
    wph
    @116
    @117
    @109
    simprll
    wph
    @116
    @117
    @109
    simprlr
    wph
    @118
    @109
    simprr
    cN
    @48
    cfn
    @4
    @108
    @115
    pmtrprfv
    syl13anc
    adantr
    sylan9eqr
    fveq2d
    oveq1d
    @126
    @133
    @128
    wceq
    @149
    @126
    @128
    @132
    iftrue
    adantl
    eqtr4d
    @149
    @126
    wn
    #
    wa
    #
    @123
    @132
    @133
    @154
    @129
    @123
    @132
    wceq
    #
    @149
    @129
    @155
    @153
    @149
    @129
    wa
    #
    @123
    @131
    @132
    @156
    @122
    @130
    @6
    cF
    @156
    @121
    @4
    @16
    @129
    @149
    @121
    @108
    @111
    cfv
    #
    @4
    @3
    @108
    @111
    fveq2
    @149
    @157
    @108
    @108
    @4
    cpr
    #
    @48
    cfv
    #
    cfv
    #
    @4
    @108
    @111
    @159
    @110
    @158
    @48
    @4
    @108
    prcom
    fveq2i
    fveq1i
    @149
    @57
    @117
    @116
    @108
    @4
    wne
    @160
    @4
    wceq
    wph
    @57
    @119
    @76
    mdetuni.n
    ad2antrr
    #
    @149
    @116
    @117
    wph
    @118
    @109
    @76
    simplrl
    #
    simprd
    @149
    @116
    @117
    @162
    simpld
    @149
    @4
    @108
    wph
    @118
    @109
    @76
    simplrr
    #
    necomd
    cN
    @48
    cfn
    @108
    @4
    @115
    pmtrprfv
    syl13anc
    syl5eq
    sylan9eqr
    fveq2d
    oveq1d
    @129
    @132
    @131
    wceq
    @149
    @129
    @131
    @18
    iftrue
    adantl
    eqtr4d
    adantlr
    @154
    @129
    wn
    #
    wa
    #
    @123
    @18
    @132
    @165
    @122
    @17
    @6
    cF
    @165
    @121
    @3
    @16
    @165
    @121
    @3
    wceq
    #
    @3
    @111
    cid
    cdif
    cdm
    #
    wcel
    #
    wn
    #
    @165
    @169
    @3
    @110
    wcel
    #
    wn
    #
    @153
    @164
    @171
    @149
    @171
    @126
    @129
    wo
    #
    wn
    @153
    @164
    wa
    @170
    @172
    @3
    @4
    @108
    va
    vex
    elpr
    notbii
    @126
    @129
    ioran
    sylbbr
    adantll
    @149
    @169
    @171
    wb
    @153
    @164
    @149
    @168
    @170
    @149
    @167
    @110
    @3
    @149
    @57
    @110
    cN
    wss
    #
    @110
    c2o
    cen
    wbr
    #
    @167
    @110
    wceq
    @161
    @149
    @118
    @173
    @162
    @4
    @108
    cN
    prssi
    syl
    #
    @149
    @174
    @109
    @163
    @149
    @118
    @174
    @109
    wb
    @162
    @4
    @108
    cN
    cN
    pr2ne
    syl
    mpbird
    #
    cN
    @110
    @48
    cfn
    @115
    pmtrmvd
    syl3anc
    eleq2d
    notbid
    ad2antrr
    mpbird
    @149
    @166
    @169
    wb
    #
    @153
    @164
    @149
    @111
    cN
    wfn
    #
    @76
    @177
    @149
    cN
    cN
    @111
    wf
    #
    @178
    @149
    @57
    @173
    @174
    @179
    @161
    @175
    @176
    cN
    @110
    @48
    cfn
    @115
    pmtrf
    syl3anc
    cN
    cN
    @111
    ffn
    syl
    @147
    @76
    simpr
    @178
    @76
    wa
    @168
    @121
    @3
    cN
    @111
    @3
    fnelnfp
    necon2bbid
    syl2anc
    ad2antrr
    mpbird
    fveq2d
    oveq1d
    @164
    @132
    @18
    wceq
    @154
    @129
    @131
    @18
    iffalse
    adantl
    eqtr4d
    pm2.61dan
    @153
    @133
    @132
    wceq
    @149
    @126
    @128
    @132
    iffalse
    adantl
    eqtr4d
    pm2.61dan
    3adant3
    mpt2eq3dva
    sylan
    fveq2d
    @92
    @139
    wceq
    @120
    @20
    @138
    @91
    @19
    @137
    cD
    va
    vb
    cN
    cN
    @18
    @136
    @18
    @136
    wceq
    #
    @76
    @77
    wa
    @126
    @180
    @126
    @18
    @131
    @136
    @126
    @17
    @130
    @6
    cF
    @3
    @4
    @16
    fveq2
    oveq1d
    @126
    @131
    @135
    iftrue
    eqtr4d
    @153
    @18
    @135
    @136
    @153
    @129
    @18
    @135
    wceq
    #
    @129
    @181
    @153
    @129
    @18
    @128
    @135
    @129
    @17
    @127
    @6
    cF
    @3
    @108
    @16
    fveq2
    oveq1d
    @129
    @128
    @18
    iftrue
    eqtr4d
    adantl
    @164
    @181
    @153
    @164
    @135
    @18
    @129
    @128
    @18
    iffalse
    eqcomd
    adantl
    pm2.61dan
    @126
    @131
    @135
    iffalse
    eqtr4d
    pm2.61i
    a1i
    mpt2eq3ia
    fveq2i
    fveq2i
    a1i
    3eqtr4d
    @112
    @98
    @125
    @92
    @112
    @97
    @124
    cD
    @112
    va
    vb
    cN
    cN
    @96
    @123
    @112
    @95
    @122
    @6
    cF
    @112
    @94
    @121
    @16
    @3
    @24
    @111
    fveq1
    fveq2d
    oveq1d
    mpt2eq3dv
    fveq2d
    eqeq1d
    syl5ibrcom
    expr
    impd
    rexlimdvva
    syl5
    3impia
    syl3an2
    eqtrd
    adantr
    @23
    @92
    @93
    wceq
    @90
    @20
    @22
    @91
    fveq2
    adantl
    @90
    @93
    @33
    wceq
    @23
    @90
    @21
    @91
    cfv
    #
    @14
    c.x
    co
    @93
    @33
    @90
    cK
    cR
    c.x
    @91
    @21
    @14
    mdetuni.k
    mdetuni.tg
    @91
    eqid
    #
    @2
    @88
    @65
    @89
    @66
    3ad2ant1
    #
    @90
    @47
    cK
    @16
    @12
    @90
    @71
    @47
    cK
    @12
    wf
    @2
    @88
    @71
    @89
    wph
    @0
    @71
    @1
    @72
    3ad2ant1
    3ad2ant1
    #
    @47
    cK
    @25
    @70
    @12
    @56
    cK
    cR
    @70
    @73
    mdetuni.k
    mgpbas
    mhmf
    syl
    @103
    ffvelrnd
    #
    @90
    cB
    cK
    cF
    cD
    @2
    @88
    @67
    @89
    @68
    3ad2ant1
    wph
    @0
    @1
    @88
    @89
    simp13
    ffvelrnd
    ringmneg1
    @90
    @182
    @32
    @14
    c.x
    @90
    @32
    @21
    @24
    @12
    cfv
    #
    c.x
    co
    #
    @21
    c.1
    @91
    cfv
    #
    c.x
    co
    @182
    @90
    @71
    @88
    @102
    @32
    @188
    wceq
    @185
    @103
    @104
    @47
    @26
    c.x
    @25
    @70
    @12
    @16
    @24
    @56
    @55
    cR
    c.x
    @70
    @73
    mdetuni.tg
    mgpplusg
    mhmlin
    syl3anc
    @90
    @187
    @189
    @21
    c.x
    @90
    @65
    @57
    @24
    @47
    cN
    cevpm
    cfv
    cdif
    wcel
    #
    @187
    @189
    wceq
    @184
    @2
    @88
    @57
    @89
    @58
    3ad2ant1
    #
    @90
    @57
    @89
    @190
    @191
    @2
    @88
    @89
    simp3
    cN
    @47
    @25
    @49
    @24
    @59
    @56
    @60
    pmtrodpm
    syl2anc
    @47
    cR
    @11
    c.1
    @24
    @91
    cN
    @10
    @10
    eqid
    @11
    eqid
    mdetuni.1r
    @56
    @183
    zrhpsgnodpm
    syl3anc
    oveq2d
    @90
    cK
    cR
    c.x
    c.1
    @91
    @21
    mdetuni.k
    mdetuni.tg
    mdetuni.1r
    @183
    @184
    @186
    rngnegr
    3eqtrrd
    oveq1d
    eqtr3d
    adantr
    3eqtrd
    @2
    cE
    @47
    wcel
    #
    @0
    wph
    @0
    @1
    simp2
    @2
    @57
    @192
    @0
    wb
    @58
    cN
    @47
    cE
    @25
    cfn
    @59
    @56
    elsymgbas
    syl
    mpbird
    mrcmndind
end
