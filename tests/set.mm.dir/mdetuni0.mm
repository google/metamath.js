include "cfv.mm"
include "cur.mm"
include "co.mm"
include "csg.mm"
include "wceq.mm"
include "cv.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "wel.mm"
include "cif.mm"
include "wral.mm"
include "wi.mm"
include "cmap.mm"
include "cab.mm"
include "wcel.mm"
include "wa.mm"
include "cgrp.mm"
include "crg.mm"
include "ringgrp.mm"
include "syl.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "cfn.mm"
include "jca.mm"
include "matring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "3syl.mm"
include "ffvelrnd.mm"
include "ccrg.mm"
include "wf.mm"
include "mdetf.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "grpsubcl.mm"
include "fmptd.mm"
include "wne.mm"
include "w3a.mm"
include "simpr1.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "3adant3.mm"
include "simp1.mm"
include "simp21.mm"
include "simp3r.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3l.mm"
include "mdetunilem1.mm"
include "syl33anc.mm"
include "3ad2ant1.mm"
include "mdetralt.mm"
include "ringrz.mm"
include "syl2anc.mm"
include "grpidcl.mm"
include "grpsubid.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "3expia.mm"
include "ralrimivvva.mm"
include "cres.mm"
include "cof.mm"
include "cdif.mm"
include "simp2ll.mm"
include "simp2lr.mm"
include "simp2rl.mm"
include "simp2rr.mm"
include "simp31.mm"
include "simp32.mm"
include "simp33.mm"
include "mdetunilem3.mm"
include "syl332anc.mm"
include "mdetrlin.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprrl.mm"
include "cabl.mm"
include "ringabl.mm"
include "ablsub4.mm"
include "syl122anc.mm"
include "ringdi.mm"
include "syl13anc.mm"
include "eqcomd.mm"
include "3eqtr2d.mm"
include "3eqtr4d.mm"
include "anassrs.mm"
include "ralrimivva.mm"
include "mdetunilem4.mm"
include "syl133anc.mm"
include "mdetrsca.mm"
include "ringsubdi.mm"
include "cmgp.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "cmn12.mm"
include "cvv.mm"
include "eqidd.mm"
include "mdet1.mm"
include "ringridm.mm"
include "sylan9eqr.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fvmptd.mm"
include "mdetunilem9.mm"
include "fveq1d.mm"
include "adantl.mm"
include "ovexd.mm"
include "fvconst2.mm"
include "3eqtr3d.mm"
include "wb.mm"
include "grpsubeq0.mm"
include "mpbid.mm"

theorem mdetuni0
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
  assume mdetuni.e: |- E = ( N maDet R )
  assume mdetuni.cr: |- ( ph -> R e. CRing )
  assume mdetuni.f: |- ( ph -> F e. B )

  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint K w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .x. w
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .+ w
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  disjoint .0. w
  disjoint .1. x
  disjoint .1. y
  disjoint .1. z
  disjoint .1. w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
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
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint a w
  disjoint b w
  disjoint c w
  disjoint d w
  disjoint e w
  disjoint f w
  disjoint a b
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
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K d
  disjoint K e
  disjoint K f
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N d
  disjoint N e
  disjoint N f
  disjoint D a
  disjoint D b
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
  disjoint .+ a
  disjoint .+ b
  disjoint .+ e
  disjoint .0. a
  disjoint .0. b
  disjoint .0. c
  disjoint .0. d
  disjoint .0. e
  disjoint .1. a
  disjoint .1. b
  disjoint .1. c
  disjoint .1. d
  disjoint .1. e
  disjoint R e
  disjoint A a
  disjoint A b
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
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint .x. a
  disjoint .x. b
  disjoint .x. c
  disjoint .x. d
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E d
  disjoint E e
  disjoint F a
  disjoint A e
  disjoint .+ c
  disjoint .+ d
  assert |- ( ph -> ( D ` F ) = ( ( D ` ( 1r ` A ) ) .x. ( E ` F ) ) )

  proof
    wph
    cF
    cD
    cfv
    #
    cA
    cur
    cfv
    #
    cD
    cfv
    #
    cF
    cE
    cfv
    #
    c.x
    co
    #
    cR
    csg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    @0
    @4
    wceq
    #
    wph
    cF
    va
    cB
    va
    cv
    #
    cD
    cfv
    #
    @2
    @9
    cE
    cfv
    #
    c.x
    co
    #
    @5
    co
    #
    cmpt
    #
    cfv
    cF
    cB
    c.0
    csn
    cxp
    #
    cfv
    #
    @6
    c.0
    wph
    cF
    @14
    @15
    wph
    vb
    vc
    vd
    ve
    cA
    cB
    @14
    c.pl
    cR
    c.x
    c.1
    cK
    cN
    ve
    cv
    #
    vc
    cv
    #
    cfv
    ve
    vd
    wel
    c.1
    c.0
    cif
    wceq
    ve
    vb
    cv
    #
    wral
    @18
    @14
    cfv
    #
    c.0
    wceq
    wi
    vd
    cN
    cN
    cmap
    co
    wral
    vc
    cB
    wral
    vb
    cab
    #
    c.0
    mdetuni.a
    mdetuni.b
    mdetuni.k
    mdetuni.0g
    mdetuni.1r
    mdetuni.pg
    mdetuni.tg
    mdetuni.n
    mdetuni.r
    wph
    va
    cB
    @13
    cK
    @14
    wph
    @9
    cB
    wcel
    #
    wa
    #
    cR
    cgrp
    wcel
    #
    @10
    cK
    wcel
    @12
    cK
    wcel
    #
    @13
    cK
    wcel
    wph
    @24
    @22
    wph
    cR
    crg
    wcel
    #
    @24
    mdetuni.r
    cR
    ringgrp
    syl
    #
    adantr
    wph
    cB
    cK
    @9
    cD
    mdetuni.ff
    ffvelrnda
    @23
    @26
    @2
    cK
    wcel
    #
    @11
    cK
    wcel
    @25
    wph
    @26
    @22
    mdetuni.r
    adantr
    wph
    @28
    @22
    wph
    cB
    cK
    @1
    cD
    mdetuni.ff
    wph
    cN
    cfn
    wcel
    #
    @26
    wa
    cA
    crg
    wcel
    @1
    cB
    wcel
    wph
    @29
    @26
    mdetuni.n
    mdetuni.r
    jca
    cA
    cR
    cN
    mdetuni.a
    matring
    cB
    cA
    @1
    mdetuni.b
    @1
    eqid
    #
    ringidcl
    3syl
    #
    ffvelrnd
    #
    adantr
    wph
    cB
    cK
    @9
    cE
    wph
    cR
    ccrg
    wcel
    #
    cB
    cK
    cE
    wf
    #
    mdetuni.cr
    cA
    cB
    cE
    cR
    cK
    cN
    mdetuni.e
    mdetuni.a
    mdetuni.b
    mdetuni.k
    mdetf
    syl
    #
    ffvelrnda
    cK
    cR
    c.x
    @2
    @11
    mdetuni.k
    mdetuni.tg
    ringcl
    syl3anc
    cK
    cR
    @5
    @10
    @12
    mdetuni.k
    @5
    eqid
    #
    grpsubcl
    syl3anc
    @14
    eqid
    #
    fmptd
    wph
    @18
    vd
    cv
    #
    wne
    #
    @18
    @17
    @19
    co
    #
    @38
    @17
    @19
    co
    #
    wceq
    #
    ve
    cN
    wral
    #
    wa
    #
    @19
    @14
    cfv
    #
    c.0
    wceq
    #
    wi
    vb
    vc
    vd
    cB
    cN
    cN
    wph
    @19
    cB
    wcel
    #
    @18
    cN
    wcel
    #
    @38
    cN
    wcel
    #
    w3a
    #
    @44
    @46
    wph
    @50
    @44
    w3a
    #
    @45
    @19
    cD
    cfv
    #
    @2
    @19
    cE
    cfv
    #
    c.x
    co
    #
    @5
    co
    #
    c.0
    @2
    c.0
    c.x
    co
    #
    @5
    co
    #
    c.0
    wph
    @50
    @45
    @55
    wceq
    #
    @44
    wph
    @50
    wa
    @47
    @58
    wph
    @47
    @48
    @49
    simpr1
    va
    @19
    @13
    @55
    cB
    @14
    va
    vb
    weq
    #
    @10
    @52
    @12
    @54
    @5
    @9
    @19
    cD
    fveq2
    @59
    @11
    @53
    @2
    c.x
    @9
    @19
    cE
    fveq2
    oveq2d
    oveq12d
    @37
    @52
    @54
    @5
    ovex
    fvmpt
    #
    syl
    3adant3
    @51
    @52
    c.0
    @54
    @56
    @5
    @51
    wph
    @47
    @18
    vw
    cv
    #
    @19
    co
    #
    @38
    @61
    @19
    co
    #
    wceq
    #
    vw
    cN
    wral
    #
    @48
    @49
    @39
    @52
    c.0
    wceq
    wph
    @50
    @44
    simp1
    wph
    @47
    @48
    @49
    @44
    simp21
    #
    @51
    @43
    @65
    wph
    @50
    @39
    @43
    simp3r
    #
    @42
    @64
    ve
    vw
    cN
    ve
    vw
    weq
    @40
    @62
    @41
    @63
    @17
    @61
    @18
    @19
    oveq2
    @17
    @61
    @38
    @19
    oveq2
    eqeq12d
    cbvralv
    sylib
    wph
    @47
    @48
    @49
    @44
    simp22
    #
    wph
    @47
    @48
    @49
    @44
    simp23
    #
    wph
    @50
    @39
    @43
    simp3l
    #
    wph
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
    @19
    @18
    @38
    cK
    cN
    c.0
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
    mdetunilem1
    syl33anc
    @51
    @53
    c.0
    @2
    c.x
    @51
    cA
    cB
    cE
    cR
    @18
    @38
    cN
    @19
    c.0
    ve
    mdetuni.e
    mdetuni.a
    mdetuni.b
    mdetuni.0g
    wph
    @50
    @33
    @44
    mdetuni.cr
    3ad2ant1
    @66
    @68
    @69
    @70
    @67
    mdetralt
    oveq2d
    oveq12d
    wph
    @50
    @57
    c.0
    wceq
    @44
    wph
    @57
    c.0
    c.0
    @5
    co
    #
    c.0
    wph
    @56
    c.0
    c.0
    @5
    wph
    @26
    @28
    @56
    c.0
    wceq
    mdetuni.r
    @32
    cK
    cR
    c.x
    @2
    c.0
    mdetuni.k
    mdetuni.tg
    mdetuni.0g
    ringrz
    syl2anc
    oveq2d
    wph
    @24
    c.0
    cK
    wcel
    #
    @71
    c.0
    wceq
    @27
    wph
    @24
    @72
    @27
    cK
    cR
    c.0
    mdetuni.k
    mdetuni.0g
    grpidcl
    syl
    cK
    cR
    @5
    c.0
    c.0
    mdetuni.k
    mdetuni.0g
    @36
    grpsubid
    syl2anc
    eqtrd
    3ad2ant1
    3eqtrd
    3expia
    ralrimivvva
    wph
    @19
    @17
    csn
    #
    cN
    cxp
    #
    cres
    #
    @18
    @74
    cres
    @38
    @74
    cres
    #
    c.pl
    cof
    co
    wceq
    #
    @19
    cN
    @73
    cdif
    cN
    cxp
    #
    cres
    #
    @18
    @78
    cres
    wceq
    #
    @79
    @38
    @78
    cres
    wceq
    #
    w3a
    #
    @45
    @20
    @38
    @14
    cfv
    #
    c.pl
    co
    #
    wceq
    #
    wi
    #
    ve
    cN
    wral
    vd
    cB
    wral
    vb
    vc
    cB
    cB
    wph
    @47
    @18
    cB
    wcel
    #
    wa
    #
    wa
    @86
    vd
    ve
    cB
    cN
    wph
    @88
    @38
    cB
    wcel
    #
    @17
    cN
    wcel
    #
    wa
    #
    @86
    wph
    @88
    @91
    wa
    #
    @82
    @85
    wph
    @92
    @82
    w3a
    #
    @55
    @18
    cD
    cfv
    #
    @38
    cD
    cfv
    #
    c.pl
    co
    #
    @2
    @18
    cE
    cfv
    #
    @38
    cE
    cfv
    #
    c.pl
    co
    #
    c.x
    co
    #
    @5
    co
    #
    @45
    @84
    @93
    @52
    @96
    @54
    @100
    @5
    @93
    wph
    @47
    @87
    @89
    @90
    @77
    @80
    @81
    @52
    @96
    wceq
    wph
    @92
    @82
    simp1
    @47
    @87
    @91
    wph
    @82
    simp2ll
    #
    @47
    @87
    @91
    wph
    @82
    simp2lr
    #
    @89
    @90
    @88
    wph
    @82
    simp2rl
    #
    @89
    @90
    @88
    wph
    @82
    simp2rr
    #
    wph
    @92
    @77
    @80
    @81
    simp31
    #
    wph
    @92
    @77
    @80
    @81
    simp32
    #
    wph
    @92
    @77
    @80
    @81
    simp33
    #
    wph
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
    @19
    @18
    @38
    @17
    cK
    cN
    c.0
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
    mdetunilem3
    syl332anc
    @93
    @53
    @99
    @2
    c.x
    @93
    cA
    cB
    cE
    c.pl
    cR
    @17
    cN
    @19
    @18
    @38
    mdetuni.e
    mdetuni.a
    mdetuni.b
    mdetuni.pg
    wph
    @92
    @33
    @82
    mdetuni.cr
    3ad2ant1
    @102
    @103
    @104
    @105
    @106
    @107
    @108
    mdetrlin
    oveq2d
    oveq12d
    wph
    @92
    @58
    @82
    wph
    @92
    wa
    #
    @47
    @58
    wph
    @47
    @87
    @91
    simprll
    @60
    syl
    3adant3
    wph
    @92
    @84
    @101
    wceq
    @82
    @109
    @84
    @94
    @2
    @97
    c.x
    co
    #
    @5
    co
    #
    @95
    @2
    @98
    c.x
    co
    #
    @5
    co
    #
    c.pl
    co
    #
    @96
    @110
    @112
    c.pl
    co
    #
    @5
    co
    #
    @101
    @109
    @20
    @111
    @83
    @113
    c.pl
    @109
    @87
    @20
    @111
    wceq
    wph
    @47
    @87
    @91
    simprlr
    #
    va
    @18
    @13
    @111
    cB
    @14
    va
    vc
    weq
    #
    @10
    @94
    @12
    @110
    @5
    @9
    @18
    cD
    fveq2
    @118
    @11
    @97
    @2
    c.x
    @9
    @18
    cE
    fveq2
    oveq2d
    oveq12d
    @37
    @94
    @110
    @5
    ovex
    fvmpt
    syl
    @109
    @89
    @83
    @113
    wceq
    #
    wph
    @88
    @89
    @90
    simprrl
    #
    va
    @38
    @13
    @113
    cB
    @14
    va
    vd
    weq
    #
    @10
    @95
    @12
    @112
    @5
    @9
    @38
    cD
    fveq2
    @121
    @11
    @98
    @2
    c.x
    @9
    @38
    cE
    fveq2
    oveq2d
    oveq12d
    @37
    @95
    @112
    @5
    ovex
    fvmpt
    #
    syl
    oveq12d
    @109
    cR
    cabl
    wcel
    #
    @94
    cK
    wcel
    @95
    cK
    wcel
    @110
    cK
    wcel
    #
    @112
    cK
    wcel
    #
    @116
    @114
    wceq
    wph
    @123
    @92
    wph
    @26
    @123
    mdetuni.r
    cR
    ringabl
    syl
    adantr
    @109
    cB
    cK
    @18
    cD
    wph
    cB
    cK
    cD
    wf
    #
    @92
    mdetuni.ff
    adantr
    #
    @117
    ffvelrnd
    @109
    cB
    cK
    @38
    cD
    @127
    @120
    ffvelrnd
    @109
    @26
    @28
    @97
    cK
    wcel
    #
    @124
    wph
    @26
    @92
    mdetuni.r
    adantr
    #
    wph
    @28
    @92
    @32
    adantr
    #
    @109
    cB
    cK
    @18
    cE
    wph
    @34
    @92
    @35
    adantr
    #
    @117
    ffvelrnd
    #
    cK
    cR
    c.x
    @2
    @97
    mdetuni.k
    mdetuni.tg
    ringcl
    syl3anc
    @109
    @26
    @28
    @98
    cK
    wcel
    #
    @125
    @129
    @130
    @109
    cB
    cK
    @38
    cE
    @131
    @120
    ffvelrnd
    #
    cK
    cR
    c.x
    @2
    @98
    mdetuni.k
    mdetuni.tg
    ringcl
    #
    syl3anc
    cK
    c.pl
    cR
    @5
    @112
    @94
    @95
    @110
    mdetuni.k
    mdetuni.pg
    @36
    ablsub4
    syl122anc
    @109
    @115
    @100
    @96
    @5
    @109
    @100
    @115
    @109
    @26
    @28
    @128
    @133
    @100
    @115
    wceq
    @129
    @130
    @132
    @134
    cK
    c.pl
    cR
    c.x
    @2
    @97
    @98
    mdetuni.k
    mdetuni.pg
    mdetuni.tg
    ringdi
    syl13anc
    eqcomd
    oveq2d
    3eqtr2d
    3adant3
    3eqtr4d
    3expia
    anassrs
    ralrimivva
    ralrimivva
    wph
    @75
    @74
    @18
    csn
    cxp
    @76
    c.x
    cof
    co
    wceq
    #
    @81
    wa
    #
    @45
    @18
    @83
    c.x
    co
    #
    wceq
    #
    wi
    #
    ve
    cN
    wral
    vd
    cB
    wral
    vb
    vc
    cB
    cK
    wph
    @47
    @18
    cK
    wcel
    #
    wa
    #
    wa
    @140
    vd
    ve
    cB
    cN
    wph
    @142
    @91
    @140
    wph
    @142
    @91
    wa
    #
    @137
    @139
    wph
    @143
    @137
    w3a
    #
    @55
    @18
    @95
    c.x
    co
    #
    @2
    @18
    @98
    c.x
    co
    #
    c.x
    co
    #
    @5
    co
    #
    @45
    @138
    @144
    @52
    @145
    @54
    @147
    @5
    @144
    wph
    @47
    @141
    @89
    @90
    @136
    @81
    @52
    @145
    wceq
    wph
    @143
    @137
    simp1
    @47
    @141
    @91
    wph
    @137
    simp2ll
    #
    @47
    @141
    @91
    wph
    @137
    simp2lr
    #
    @89
    @90
    @142
    wph
    @137
    simp2rl
    #
    @89
    @90
    @142
    wph
    @137
    simp2rr
    #
    wph
    @143
    @136
    @81
    simp3l
    #
    wph
    @143
    @136
    @81
    simp3r
    #
    wph
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
    @19
    @18
    @38
    @17
    cK
    cN
    c.0
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
    mdetunilem4
    syl133anc
    @144
    @53
    @146
    @2
    c.x
    @144
    cA
    cB
    cE
    cR
    c.x
    @17
    cK
    cN
    @19
    @18
    @38
    mdetuni.e
    mdetuni.a
    mdetuni.b
    mdetuni.k
    mdetuni.tg
    wph
    @143
    @33
    @137
    mdetuni.cr
    3ad2ant1
    @149
    @150
    @151
    @152
    @153
    @154
    mdetrsca
    oveq2d
    oveq12d
    wph
    @143
    @58
    @137
    wph
    @143
    wa
    #
    @47
    @58
    wph
    @47
    @141
    @91
    simprll
    @60
    syl
    3adant3
    wph
    @143
    @138
    @148
    wceq
    @137
    @155
    @138
    @18
    @113
    c.x
    co
    @145
    @18
    @112
    c.x
    co
    #
    @5
    co
    @148
    @155
    @83
    @113
    @18
    c.x
    @155
    @89
    @119
    wph
    @142
    @89
    @90
    simprrl
    #
    @122
    syl
    oveq2d
    @155
    cK
    cR
    c.x
    @5
    @18
    @95
    @112
    mdetuni.k
    mdetuni.tg
    @36
    wph
    @26
    @143
    mdetuni.r
    adantr
    #
    wph
    @47
    @141
    @91
    simprlr
    #
    @155
    cB
    cK
    @38
    cD
    wph
    @126
    @143
    mdetuni.ff
    adantr
    @157
    ffvelrnd
    @155
    @26
    @28
    @133
    @125
    @158
    wph
    @28
    @143
    @32
    adantr
    #
    @155
    cB
    cK
    @38
    cE
    wph
    @34
    @143
    @35
    adantr
    @157
    ffvelrnd
    #
    @135
    syl3anc
    ringsubdi
    @155
    @156
    @147
    @145
    @5
    @155
    cR
    cmgp
    cfv
    #
    ccmn
    wcel
    #
    @141
    @28
    @133
    @156
    @147
    wceq
    wph
    @163
    @143
    wph
    @33
    @163
    mdetuni.cr
    cR
    @162
    @162
    eqid
    #
    crngmgp
    syl
    adantr
    @159
    @160
    @161
    cK
    c.x
    @162
    @18
    @2
    @98
    cK
    cR
    @162
    @164
    mdetuni.k
    mgpbas
    cR
    c.x
    @162
    @164
    mdetuni.tg
    mgpplusg
    cmn12
    syl13anc
    oveq2d
    3eqtrd
    3adant3
    3eqtr4d
    3expia
    anassrs
    ralrimivva
    ralrimivva
    wph
    va
    @1
    @13
    c.0
    cB
    @14
    cvv
    wph
    @14
    eqidd
    #
    @9
    @1
    wceq
    #
    wph
    @13
    @2
    @2
    @1
    cE
    cfv
    #
    c.x
    co
    #
    @5
    co
    #
    c.0
    @166
    @10
    @2
    @12
    @168
    @5
    @9
    @1
    cD
    fveq2
    @166
    @11
    @167
    @2
    c.x
    @9
    @1
    cE
    fveq2
    oveq2d
    oveq12d
    wph
    @169
    @2
    @2
    @5
    co
    #
    c.0
    wph
    @168
    @2
    @2
    @5
    wph
    @168
    @2
    c.1
    c.x
    co
    #
    @2
    wph
    @167
    c.1
    @2
    c.x
    wph
    @33
    @29
    @167
    c.1
    wceq
    mdetuni.cr
    mdetuni.n
    cA
    cE
    cR
    c.1
    @1
    cN
    mdetuni.e
    mdetuni.a
    @30
    mdetuni.1r
    mdet1
    syl2anc
    oveq2d
    wph
    @26
    @28
    @171
    @2
    wceq
    mdetuni.r
    @32
    cK
    cR
    c.x
    c.1
    @2
    mdetuni.k
    mdetuni.tg
    mdetuni.1r
    ringridm
    syl2anc
    eqtrd
    oveq2d
    wph
    @24
    @28
    @170
    c.0
    wceq
    @27
    @32
    cK
    cR
    @5
    @2
    c.0
    mdetuni.k
    mdetuni.0g
    @36
    grpsubid
    syl2anc
    eqtrd
    sylan9eqr
    @31
    c.0
    cvv
    wcel
    wph
    c.0
    cR
    c0g
    cfv
    cvv
    mdetuni.0g
    cR
    c0g
    fvex
    eqeltri
    #
    a1i
    fvmptd
    @21
    eqid
    mdetunilem9
    fveq1d
    wph
    va
    cF
    @13
    @6
    cB
    @14
    cvv
    @165
    @9
    cF
    wceq
    #
    @13
    @6
    wceq
    wph
    @173
    @10
    @0
    @12
    @4
    @5
    @9
    cF
    cD
    fveq2
    @173
    @11
    @3
    @2
    c.x
    @9
    cF
    cE
    fveq2
    oveq2d
    oveq12d
    adantl
    mdetuni.f
    wph
    @0
    @4
    @5
    ovexd
    fvmptd
    wph
    cF
    cB
    wcel
    @16
    c.0
    wceq
    mdetuni.f
    cB
    c.0
    cF
    @172
    fvconst2
    syl
    3eqtr3d
    wph
    @24
    @0
    cK
    wcel
    @4
    cK
    wcel
    #
    @7
    @8
    wb
    @27
    wph
    cB
    cK
    cF
    cD
    mdetuni.ff
    mdetuni.f
    ffvelrnd
    wph
    @26
    @28
    @3
    cK
    wcel
    @174
    mdetuni.r
    @32
    wph
    cB
    cK
    cF
    cE
    @35
    mdetuni.f
    ffvelrnd
    cK
    cR
    c.x
    @2
    @3
    mdetuni.k
    mdetuni.tg
    ringcl
    syl3anc
    cK
    cR
    @5
    @0
    @4
    c.0
    mdetuni.k
    mdetuni.0g
    @36
    grpsubeq0
    syl3anc
    mpbid
end
