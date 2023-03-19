include "cfv.mm"
include "co.mm"
include "cmul.mm"
include "csmat.mm"
include "c1.mm"
include "cfz.mm"
include "cminmar1.mm"
include "wcel.mm"
include "wceq.mm"
include "maducoevalmin1.mm"
include "syl3anc.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "fzfid.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "syl.mm"
include "minmar1cl.mm"
include "syl22anc.mm"
include "syl5eqel.mm"
include "mdetpmtr12.mm"
include "cur.mm"
include "cmarrep.mm"
include "cv.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "w3a.mm"
include "wa.mm"
include "simplr.mm"
include "fveq2d.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "simpr.mm"
include "oveq12d.mm"
include "eqid.mm"
include "minmar1eval.mm"
include "syl122anc.mm"
include "iftruei.mm"
include "eqtri.mm"
include "a1i.mm"
include "3eqtrrd.mm"
include "wn.mm"
include "oveq1d.mm"
include "simp3.mm"
include "csymg.mm"
include "symgfv.mm"
include "syl2anc.mm"
include "iftrued.mm"
include "ccnv.mm"
include "wf1o.mm"
include "symgbasf1o.mm"
include "f1ocnvfv1.mm"
include "cuz.mm"
include "cn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "eqtr3d.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "con3d.mm"
include "imp.mm"
include "iffalsed.mm"
include "ifeqda.mm"
include "cvv.mm"
include "simp2.mm"
include "adantr.mm"
include "ovexd.mm"
include "oveqi.mm"
include "mpt2eq3ia.mm"
include "ovmpt4g.mm"
include "mpt2eq3dva.mm"
include "cbs.mm"
include "matecld.mm"
include "matbas2d.mm"
include "ringidcl.mm"
include "marrepval.mm"
include "3eqtr4d.mm"
include "csubma.mm"
include "cmin.mm"
include "cmat.mm"
include "csn.mm"
include "cdif.mm"
include "submaval.mm"
include "fzdif2.mm"
include "mpt2eq12.mm"
include "wss.mm"
include "difssd.mm"
include "eqsstr3d.mm"
include "submabas.mm"
include "eqeltrd.mm"
include "mdetcl.mm"
include "ringlidm.mm"
include "cmdat.mm"
include "cmulr.mm"
include "smadiadetr.mm"
include "fveq1i.mm"
include "eqeq12i.mm"
include "sylibr.mm"
include "fveq1d.mm"
include "oveq2d.mm"
include "submat1n.mm"
include "submatminr1.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem madjusmdetlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vk: setvar k
  let vl: setvar l
  assume madjusmdet.b: |- B = ( Base ` A )
  assume madjusmdet.a: |- A = ( ( 1 ... N ) Mat R )
  assume madjusmdet.d: |- D = ( ( 1 ... N ) maDet R )
  assume madjusmdet.k: |- K = ( ( 1 ... N ) maAdju R )
  assume madjusmdet.t: |- .x. = ( .r ` R )
  assume madjusmdet.z: |- Z = ( ZRHom ` R )
  assume madjusmdet.e: |- E = ( ( 1 ... ( N - 1 ) ) maDet R )
  assume madjusmdet.n: |- ( ph -> N e. NN )
  assume madjusmdet.r: |- ( ph -> R e. CRing )
  assume madjusmdet.i: |- ( ph -> I e. ( 1 ... N ) )
  assume madjusmdet.j: |- ( ph -> J e. ( 1 ... N ) )
  assume madjusmdet.m: |- ( ph -> M e. B )
  assume madjusmdetlem1.g: |- G = ( Base ` ( SymGrp ` ( 1 ... N ) ) )
  assume madjusmdetlem1.s: |- S = ( pmSgn ` ( 1 ... N ) )
  assume madjusmdetlem1.u: |- U = ( I ( ( ( 1 ... N ) minMatR1 R ) ` M ) J )
  assume madjusmdetlem1.w: |- W = ( i e. ( 1 ... N ) , j e. ( 1 ... N ) |-> ( ( P ` i ) U ( Q ` j ) ) )
  assume madjusmdetlem1.p: |- ( ph -> P e. G )
  assume madjusmdetlem1.q: |- ( ph -> Q e. G )
  assume madjusmdetlem1.1: |- ( ph -> ( P ` N ) = I )
  assume madjusmdetlem1.2: |- ( ph -> ( Q ` N ) = J )
  assume madjusmdetlem1.3: |- ( ph -> ( I ( subMat1 ` U ) J ) = ( N ( subMat1 ` W ) N ) )

  disjoint G i
  disjoint G j
  disjoint i j
  disjoint W i
  disjoint W j
  disjoint U i
  disjoint U j
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint I i
  disjoint I j
  disjoint J i
  disjoint J j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint Q i
  disjoint Q j
  disjoint R i
  disjoint R j
  disjoint i ph
  disjoint j ph
  disjoint I k
  disjoint I l
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint J k
  disjoint J l
  disjoint M k
  disjoint M l
  disjoint N k
  disjoint N l
  disjoint P k
  disjoint P l
  disjoint Q k
  disjoint Q l
  disjoint R k
  disjoint R l
  assert |- ( ph -> ( J ( K ` M ) I ) = ( ( Z ` ( ( S ` P ) x. ( S ` Q ) ) ) .x. ( E ` ( I ( subMat1 ` M ) J ) ) ) )

  proof
    wph
    cJ
    cI
    cM
    cK
    cfv
    co
    #
    cU
    cD
    cfv
    #
    cP
    cS
    cfv
    cQ
    cS
    cfv
    cmul
    co
    cZ
    cfv
    #
    cW
    cD
    cfv
    #
    c.x
    co
    @2
    cI
    cJ
    cM
    csmat
    cfv
    co
    #
    cE
    cfv
    #
    c.x
    co
    wph
    @0
    cI
    cJ
    cM
    c1
    cN
    cfz
    co
    #
    cR
    cminmar1
    co
    #
    cfv
    co
    #
    cD
    cfv
    #
    @1
    wph
    cM
    cB
    wcel
    #
    cJ
    @6
    wcel
    #
    cI
    @6
    wcel
    #
    @0
    @9
    wceq
    madjusmdet.m
    madjusmdet.j
    madjusmdet.i
    cA
    cB
    cD
    cR
    cI
    cJ
    cK
    cM
    @6
    madjusmdet.a
    madjusmdet.b
    madjusmdet.d
    madjusmdet.k
    maducoevalmin1
    syl3anc
    cU
    @8
    cD
    madjusmdetlem1.u
    fveq2i
    syl6eqr
    wph
    cA
    cB
    cD
    cP
    cQ
    cR
    cS
    c.x
    vi
    vj
    cW
    cG
    cU
    @6
    cZ
    madjusmdet.a
    madjusmdet.b
    madjusmdet.d
    madjusmdetlem1.g
    madjusmdetlem1.s
    madjusmdet.z
    madjusmdet.t
    madjusmdetlem1.w
    madjusmdet.r
    wph
    c1
    cN
    fzfid
    #
    wph
    cU
    @8
    cB
    madjusmdetlem1.u
    wph
    cR
    crg
    wcel
    #
    @10
    @12
    @11
    @8
    cB
    wcel
    wph
    cR
    ccrg
    wcel
    #
    @14
    madjusmdet.r
    cR
    crngring
    syl
    #
    madjusmdet.m
    madjusmdet.i
    madjusmdet.j
    cA
    cB
    cR
    cI
    cJ
    cM
    @6
    madjusmdet.a
    madjusmdet.b
    minmar1cl
    syl22anc
    syl5eqel
    #
    madjusmdetlem1.p
    madjusmdetlem1.q
    mdetpmtr12
    wph
    @3
    @5
    @2
    c.x
    wph
    @3
    cN
    cN
    cW
    csmat
    cfv
    co
    #
    cE
    cfv
    #
    @5
    wph
    cN
    cN
    cW
    cR
    cur
    cfv
    #
    @6
    cR
    cmarrep
    co
    #
    co
    co
    #
    cD
    cfv
    #
    @3
    @19
    wph
    @22
    cW
    cD
    wph
    vi
    vj
    @6
    @6
    vi
    cv
    #
    cN
    wceq
    #
    vj
    cv
    #
    cN
    wceq
    #
    @20
    cR
    c0g
    cfv
    #
    cif
    #
    @24
    @26
    cW
    co
    #
    cif
    #
    cmpt2
    #
    vi
    vj
    @6
    @6
    @24
    cP
    cfv
    #
    @26
    cQ
    cfv
    #
    @8
    co
    #
    cmpt2
    #
    @22
    cW
    wph
    vi
    vj
    @6
    @6
    @31
    @35
    wph
    @24
    @6
    wcel
    #
    @26
    @6
    wcel
    #
    w3a
    #
    @25
    @29
    @30
    @35
    @39
    @25
    wa
    #
    @27
    @20
    @28
    @35
    @40
    @27
    wa
    #
    @35
    cI
    cJ
    @8
    co
    #
    cI
    cI
    wceq
    #
    cJ
    cJ
    wceq
    #
    @20
    @28
    cif
    #
    cI
    cJ
    cM
    co
    #
    cif
    #
    @20
    @41
    @33
    cI
    @34
    cJ
    @8
    @41
    @33
    cN
    cP
    cfv
    #
    cI
    @41
    @24
    cN
    cP
    @39
    @25
    @27
    simplr
    fveq2d
    @39
    @48
    cI
    wceq
    #
    @25
    @27
    wph
    @37
    @49
    @38
    madjusmdetlem1.1
    3ad2ant1
    #
    ad2antrr
    eqtrd
    @41
    @34
    cN
    cQ
    cfv
    #
    cJ
    @41
    @26
    cN
    cQ
    @40
    @27
    simpr
    fveq2d
    @39
    @51
    cJ
    wceq
    #
    @25
    @27
    wph
    @37
    @52
    @38
    madjusmdetlem1.2
    3ad2ant1
    ad2antrr
    eqtrd
    oveq12d
    @41
    @10
    @12
    @11
    @12
    @11
    @42
    @47
    wceq
    @39
    @10
    @25
    @27
    wph
    @37
    @10
    @38
    madjusmdet.m
    3ad2ant1
    #
    ad2antrr
    @39
    @12
    @25
    @27
    wph
    @37
    @12
    @38
    madjusmdet.i
    3ad2ant1
    #
    ad2antrr
    #
    @39
    @11
    @25
    @27
    wph
    @37
    @11
    @38
    madjusmdet.j
    3ad2ant1
    #
    ad2antrr
    #
    @55
    @57
    cA
    cB
    @7
    cR
    @20
    cI
    cJ
    cI
    cJ
    cM
    @6
    @28
    madjusmdet.a
    madjusmdet.b
    @7
    eqid
    #
    @20
    eqid
    #
    @28
    eqid
    #
    minmar1eval
    syl122anc
    @47
    @20
    wceq
    @41
    @47
    @45
    @20
    @43
    @45
    @46
    cI
    eqid
    #
    iftruei
    @44
    @20
    @28
    cJ
    eqid
    iftruei
    eqtri
    a1i
    3eqtrrd
    @40
    @27
    wn
    #
    wa
    #
    @35
    cI
    @34
    @8
    co
    #
    @43
    @34
    cJ
    wceq
    #
    @20
    @28
    cif
    #
    cI
    @34
    cM
    co
    #
    cif
    #
    @28
    @63
    @33
    cI
    @34
    @8
    @63
    @33
    @48
    cI
    @63
    @24
    cN
    cP
    @39
    @25
    @62
    simplr
    fveq2d
    @39
    @49
    @25
    @62
    @50
    ad2antrr
    eqtrd
    oveq1d
    @63
    @10
    @12
    @11
    @12
    @34
    @6
    wcel
    #
    @64
    @68
    wceq
    @39
    @10
    @25
    @62
    @53
    ad2antrr
    @39
    @12
    @25
    @62
    @54
    ad2antrr
    #
    @39
    @11
    @25
    @62
    @56
    ad2antrr
    @70
    @39
    @69
    @25
    @62
    @39
    cQ
    cG
    wcel
    #
    @38
    @69
    wph
    @37
    @71
    @38
    madjusmdetlem1.q
    3ad2ant1
    #
    wph
    @37
    @38
    simp3
    #
    @6
    cG
    cQ
    @6
    csymg
    cfv
    #
    @26
    @74
    eqid
    #
    madjusmdetlem1.g
    symgfv
    syl2anc
    #
    ad2antrr
    cA
    cB
    @7
    cR
    @20
    cI
    @34
    cI
    cJ
    cM
    @6
    @28
    madjusmdet.a
    madjusmdet.b
    @58
    @59
    @60
    minmar1eval
    syl122anc
    @63
    @68
    @66
    @28
    @63
    @43
    @66
    @67
    @43
    @63
    @61
    a1i
    iftrued
    @63
    @65
    @20
    @28
    @40
    @62
    @65
    wn
    @40
    @65
    @27
    @40
    @65
    @27
    @40
    @65
    wa
    #
    @34
    cQ
    ccnv
    #
    cfv
    #
    cJ
    @78
    cfv
    #
    @26
    cN
    @77
    @34
    cJ
    @78
    @40
    @65
    simpr
    fveq2d
    @77
    @6
    @6
    cQ
    wf1o
    #
    @38
    @79
    @26
    wceq
    @39
    @81
    @25
    @65
    @39
    @71
    @81
    @72
    @6
    cG
    cQ
    @74
    @75
    madjusmdetlem1.g
    symgbasf1o
    #
    syl
    ad2antrr
    @39
    @38
    @25
    @65
    @73
    ad2antrr
    @6
    @6
    @26
    cQ
    f1ocnvfv1
    syl2anc
    @39
    @80
    cN
    wceq
    #
    @25
    @65
    wph
    @37
    @83
    @38
    wph
    @51
    @78
    cfv
    #
    @80
    cN
    wph
    @51
    cJ
    @78
    madjusmdetlem1.2
    fveq2d
    wph
    @81
    cN
    @6
    wcel
    #
    @84
    cN
    wceq
    wph
    @71
    @81
    madjusmdetlem1.q
    @82
    syl
    wph
    cN
    c1
    cuz
    cfv
    #
    wcel
    #
    @85
    wph
    cN
    cn
    @86
    madjusmdet.n
    nnuz
    syl6eleq
    #
    c1
    cN
    eluzfz2
    syl
    #
    @6
    @6
    cN
    cQ
    f1ocnvfv1
    syl2anc
    eqtr3d
    3ad2ant1
    ad2antrr
    3eqtr3d
    ex
    con3d
    imp
    iffalsed
    eqtrd
    3eqtrrd
    ifeqda
    @39
    @25
    wn
    #
    wa
    #
    @37
    @38
    @35
    cvv
    wcel
    @30
    @35
    wceq
    @39
    @37
    @90
    wph
    @37
    @38
    simp2
    #
    adantr
    @39
    @38
    @90
    @73
    adantr
    @91
    @33
    @34
    @8
    ovexd
    vi
    vj
    @6
    @6
    @35
    cW
    cvv
    cW
    vi
    vj
    @6
    @6
    @33
    @34
    cU
    co
    #
    cmpt2
    #
    @36
    madjusmdetlem1.w
    vi
    vj
    @6
    @6
    @93
    @35
    @93
    @35
    wceq
    @37
    @38
    wa
    cU
    @8
    @33
    @34
    madjusmdetlem1.u
    oveqi
    a1i
    mpt2eq3ia
    eqtri
    #
    ovmpt4g
    syl3anc
    ifeqda
    mpt2eq3dva
    wph
    cW
    cB
    wcel
    #
    @20
    cR
    cbs
    cfv
    #
    wcel
    #
    @85
    @85
    @22
    @32
    wceq
    wph
    cW
    @94
    cB
    madjusmdetlem1.w
    wph
    vi
    vj
    cA
    cB
    @93
    cR
    @97
    @6
    ccrg
    madjusmdet.a
    @97
    eqid
    #
    madjusmdet.b
    @13
    madjusmdet.r
    @39
    cA
    cB
    cR
    @33
    @34
    @97
    cU
    @6
    madjusmdet.a
    @99
    madjusmdet.b
    @39
    cP
    cG
    wcel
    #
    @37
    @33
    @6
    wcel
    wph
    @37
    @100
    @38
    madjusmdetlem1.p
    3ad2ant1
    @92
    @6
    cG
    cP
    @74
    @24
    @75
    madjusmdetlem1.g
    symgfv
    syl2anc
    @76
    wph
    @37
    cU
    cB
    wcel
    @38
    @17
    3ad2ant1
    matecld
    matbas2d
    syl5eqel
    #
    wph
    @14
    @98
    @16
    @97
    cR
    @20
    @99
    @59
    ringidcl
    syl
    #
    @89
    @89
    cA
    cB
    @21
    cR
    @20
    vi
    vj
    cN
    cN
    cW
    @6
    @28
    madjusmdet.a
    madjusmdet.b
    @21
    eqid
    @60
    marrepval
    syl22anc
    cW
    @36
    wceq
    wph
    @95
    a1i
    3eqtr4d
    fveq2d
    wph
    @20
    cN
    cN
    cW
    @6
    cR
    csubma
    co
    #
    cfv
    co
    #
    cE
    cfv
    #
    c.x
    co
    #
    @105
    @23
    @19
    wph
    @14
    @105
    @97
    wcel
    #
    @106
    @105
    wceq
    @16
    wph
    @15
    @104
    c1
    cN
    c1
    cmin
    co
    cfz
    co
    #
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    @107
    madjusmdet.r
    wph
    @104
    vi
    vj
    @108
    @108
    @30
    cmpt2
    #
    @110
    wph
    @104
    vi
    vj
    @6
    cN
    csn
    #
    cdif
    #
    @113
    @30
    cmpt2
    #
    @111
    wph
    @96
    @85
    @85
    @104
    @114
    wceq
    @101
    @89
    @89
    cA
    cB
    @103
    cR
    vi
    vj
    cN
    cN
    cW
    @6
    madjusmdet.a
    @103
    eqid
    madjusmdet.b
    submaval
    syl3anc
    wph
    @113
    @108
    wceq
    #
    @115
    @114
    @111
    wceq
    wph
    @87
    @115
    @88
    c1
    cN
    fzdif2
    syl
    #
    @116
    vi
    vj
    @113
    @113
    @108
    @108
    @30
    mpt2eq12
    syl2anc
    eqtrd
    wph
    @96
    @108
    @6
    wss
    @111
    @110
    wcel
    @101
    wph
    @108
    @113
    @6
    @116
    wph
    @6
    @112
    difssd
    eqsstr3d
    cA
    cB
    @108
    cR
    vi
    vj
    cW
    @6
    madjusmdet.a
    madjusmdet.b
    submabas
    syl2anc
    eqeltrd
    @109
    @110
    cE
    cR
    @97
    @104
    @108
    madjusmdet.e
    @109
    eqid
    @110
    eqid
    @99
    mdetcl
    syl2anc
    @97
    cR
    c.x
    @20
    @105
    @99
    madjusmdet.t
    @59
    ringlidm
    syl2anc
    wph
    @23
    @20
    @104
    @113
    cR
    cmdat
    co
    #
    cfv
    #
    c.x
    co
    #
    @106
    wph
    @22
    @6
    cR
    cmdat
    co
    #
    cfv
    #
    @20
    @118
    cR
    cmulr
    cfv
    #
    co
    #
    wceq
    #
    @23
    @119
    wceq
    wph
    @15
    cW
    @6
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    @85
    @98
    @124
    madjusmdet.r
    wph
    cW
    cB
    @126
    @101
    cB
    cA
    cbs
    cfv
    @126
    madjusmdet.b
    cA
    @125
    cbs
    madjusmdet.a
    fveq2i
    eqtri
    syl6eleq
    @89
    @102
    cR
    @20
    cN
    cW
    @6
    smadiadetr
    syl22anc
    @23
    @121
    @119
    @123
    @22
    cD
    @120
    madjusmdet.d
    fveq1i
    c.x
    @122
    @20
    @118
    madjusmdet.t
    oveqi
    eqeq12i
    sylibr
    wph
    @118
    @105
    @20
    c.x
    wph
    @104
    @117
    cE
    wph
    @117
    @108
    cR
    cmdat
    co
    cE
    wph
    @113
    @108
    cR
    cmdat
    @116
    oveq1d
    madjusmdet.e
    syl6eqr
    fveq1d
    oveq2d
    eqtrd
    wph
    @18
    @104
    cE
    wph
    cN
    cn
    wcel
    @96
    @18
    @104
    wceq
    madjusmdet.n
    @101
    cA
    cB
    cR
    cW
    cN
    madjusmdet.a
    madjusmdet.b
    submat1n
    syl2anc
    fveq2d
    3eqtr4d
    eqtr3d
    wph
    @4
    @18
    cE
    wph
    @4
    cI
    cJ
    cU
    csmat
    cfv
    co
    @18
    wph
    cA
    cB
    cR
    cU
    cI
    cJ
    cM
    cN
    madjusmdet.a
    madjusmdet.b
    madjusmdet.n
    madjusmdet.i
    madjusmdet.j
    @16
    madjusmdet.m
    madjusmdetlem1.u
    submatminr1
    madjusmdetlem1.3
    eqtrd
    fveq2d
    eqtr4d
    oveq2d
    3eqtrd
end
