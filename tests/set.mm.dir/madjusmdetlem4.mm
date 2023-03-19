include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "c1.mm"
include "cfz.mm"
include "cpsgn.mm"
include "cmul.mm"
include "csmat.mm"
include "cneg.mm"
include "caddc.mm"
include "cexp.mm"
include "cminmar1.mm"
include "csymg.mm"
include "cbs.mm"
include "cv.mm"
include "cmpt2.mm"
include "eqid.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "cbvmpt2v.mm"
include "wcel.mm"
include "fzto1st.mm"
include "syl.mm"
include "cminusg.mm"
include "cuz.mm"
include "cn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "symginv.mm"
include "cgrp.mm"
include "cfn.mm"
include "fzfid.mm"
include "symggrp.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "wa.mm"
include "cplusg.mm"
include "symgov.mm"
include "symgcl.mm"
include "wfun.mm"
include "cdm.mm"
include "wf1o.mm"
include "wf1.mm"
include "symgbasf1o.mm"
include "f1of1.mm"
include "wf.mm"
include "df-f1.mm"
include "simprbi.mm"
include "3syl.mm"
include "f1ocnv.mm"
include "f1odm.mm"
include "eleqtrrd.mm"
include "fvco.mm"
include "fzto1stinvn.mm"
include "fveq2d.mm"
include "fzto1stfv1.mm"
include "3eqtrd.mm"
include "crg.mm"
include "ccrg.mm"
include "crngring.mm"
include "minmar1cl.mm"
include "syl22anc.mm"
include "madjusmdetlem3.mm"
include "madjusmdetlem1.mm"
include "psgnco.mm"
include "syl3anc.mm"
include "psgnfzto1st.mm"
include "psgninv.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "1cnd.mm"
include "negcld.mm"
include "fz1ssnn.mm"
include "sseldi.mm"
include "nnnn0d.mm"
include "cn0.mm"
include "1nn0.mm"
include "a1i.mm"
include "nn0addcld.mm"
include "expcld.mm"
include "mul4d.mm"
include "expaddd.mm"
include "c2.mm"
include "nncnd.mm"
include "add4d.mm"
include "1p1e2.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "2nn0.mm"
include "neg1sqe1.mm"
include "mulid1d.mm"
include "eqtr3d.mm"
include "cz.mm"
include "cpr.mm"
include "nn0zd.mm"
include "m1expcl2.mm"
include "1neg1t1neg1.mm"

theorem madjusmdetlem4
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  let vl: setvar l
  let cX: class X
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
  assume madjusmdetlem2.p: |- P = ( i e. ( 1 ... N ) |-> if ( i = 1 , I , if ( i <_ I , ( i - 1 ) , i ) ) )
  assume madjusmdetlem2.s: |- S = ( i e. ( 1 ... N ) |-> if ( i = 1 , N , if ( i <_ N , ( i - 1 ) , i ) ) )
  assume madjusmdetlem4.q: |- Q = ( j e. ( 1 ... N ) |-> if ( j = 1 , J , if ( j <_ J , ( j - 1 ) , j ) ) )
  assume madjusmdetlem4.t: |- T = ( j e. ( 1 ... N ) |-> if ( j = 1 , N , if ( j <_ N , ( j - 1 ) , j ) ) )

  disjoint I i
  disjoint S i
  disjoint S j
  disjoint i j
  disjoint T i
  disjoint T j
  disjoint i ph
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
  disjoint I x
  disjoint i x
  disjoint S k
  disjoint S l
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint T k
  disjoint T l
  disjoint X x
  disjoint N x
  disjoint ph x
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
  assert |- ( ph -> ( J ( K ` M ) I ) = ( ( Z ` ( -u 1 ^ ( I + J ) ) ) .x. ( E ` ( I ( subMat1 ` M ) J ) ) ) )

  proof
    wph
    cJ
    cI
    cM
    cK
    cfv
    co
    cP
    cS
    ccnv
    #
    ccom
    #
    c1
    cN
    cfz
    co
    #
    cpsgn
    cfv
    #
    cfv
    #
    cQ
    cT
    ccnv
    #
    ccom
    #
    @3
    cfv
    #
    cmul
    co
    #
    cZ
    cfv
    #
    cI
    cJ
    cM
    csmat
    cfv
    co
    cE
    cfv
    #
    c.x
    co
    c1
    cneg
    #
    cI
    cJ
    caddc
    co
    #
    cexp
    co
    #
    cZ
    cfv
    #
    @10
    c.x
    co
    wph
    cA
    cB
    cD
    @1
    @6
    cR
    @3
    c.x
    cI
    cJ
    cM
    @2
    cR
    cminmar1
    co
    cfv
    co
    #
    vi
    vj
    cE
    @2
    csymg
    cfv
    #
    cbs
    cfv
    #
    cI
    cJ
    cK
    cM
    cN
    vk
    vl
    @2
    @2
    vk
    cv
    #
    @1
    cfv
    #
    vl
    cv
    #
    @6
    cfv
    #
    @15
    co
    #
    cmpt2
    #
    cZ
    madjusmdet.b
    madjusmdet.a
    madjusmdet.d
    madjusmdet.k
    madjusmdet.t
    madjusmdet.z
    madjusmdet.e
    madjusmdet.n
    madjusmdet.r
    madjusmdet.i
    madjusmdet.j
    madjusmdet.m
    @17
    eqid
    #
    @3
    eqid
    #
    @15
    eqid
    vk
    vl
    vi
    vj
    @2
    @2
    @22
    vi
    cv
    #
    @1
    cfv
    #
    vj
    cv
    #
    @6
    cfv
    #
    @15
    co
    @27
    @21
    @15
    co
    @18
    @26
    wceq
    @19
    @27
    @21
    @15
    @18
    @26
    @1
    fveq2
    oveq1d
    @20
    @28
    wceq
    @21
    @29
    @27
    @15
    @20
    @28
    @6
    fveq2
    oveq2d
    cbvmpt2v
    #
    wph
    cP
    @17
    wcel
    #
    @0
    @17
    wcel
    #
    @1
    @17
    wcel
    wph
    cI
    @2
    wcel
    #
    @31
    madjusmdet.i
    @17
    @2
    cP
    vi
    @16
    cI
    cN
    @2
    eqid
    #
    madjusmdetlem2.p
    @16
    eqid
    #
    @24
    fzto1st
    syl
    #
    wph
    cS
    @16
    cminusg
    cfv
    #
    cfv
    #
    @0
    @17
    wph
    cS
    @17
    wcel
    #
    @38
    @0
    wceq
    wph
    cN
    @2
    wcel
    #
    @39
    wph
    cN
    c1
    cuz
    cfv
    #
    wcel
    @40
    wph
    cN
    cn
    @41
    madjusmdet.n
    nnuz
    syl6eleq
    c1
    cN
    eluzfz2
    syl
    #
    @17
    @2
    cS
    vi
    @16
    cN
    cN
    @34
    madjusmdetlem2.s
    @35
    @24
    fzto1st
    syl
    #
    @2
    @17
    cS
    @16
    @37
    @35
    @24
    @37
    eqid
    #
    symginv
    syl
    wph
    @16
    cgrp
    wcel
    #
    @39
    @38
    @17
    wcel
    wph
    @2
    cfn
    wcel
    #
    @45
    wph
    c1
    cN
    fzfid
    #
    @2
    @16
    cfn
    @35
    symggrp
    syl
    #
    @43
    @17
    @16
    @37
    cS
    @24
    @44
    grpinvcl
    syl2anc
    eqeltrrd
    #
    @31
    @32
    wa
    cP
    @0
    @16
    cplusg
    cfv
    #
    co
    @1
    @17
    @2
    @17
    @50
    @16
    cP
    @0
    @35
    @24
    @50
    eqid
    #
    symgov
    @2
    @17
    @50
    @16
    cP
    @0
    @35
    @24
    @51
    symgcl
    eqeltrrd
    syl2anc
    wph
    cQ
    @17
    wcel
    #
    @5
    @17
    wcel
    #
    @6
    @17
    wcel
    wph
    cJ
    @2
    wcel
    #
    @52
    madjusmdet.j
    @17
    @2
    cQ
    vj
    @16
    cJ
    cN
    @34
    madjusmdetlem4.q
    @35
    @24
    fzto1st
    syl
    #
    wph
    cT
    @37
    cfv
    #
    @5
    @17
    wph
    cT
    @17
    wcel
    #
    @56
    @5
    wceq
    wph
    @40
    @57
    @42
    @17
    @2
    cT
    vj
    @16
    cN
    cN
    @34
    madjusmdetlem4.t
    @35
    @24
    fzto1st
    syl
    #
    @2
    @17
    cT
    @16
    @37
    @35
    @24
    @44
    symginv
    syl
    wph
    @45
    @57
    @56
    @17
    wcel
    @48
    @58
    @17
    @16
    @37
    cT
    @24
    @44
    grpinvcl
    syl2anc
    eqeltrrd
    #
    @52
    @53
    wa
    cQ
    @5
    @50
    co
    @6
    @17
    @2
    @17
    @50
    @16
    cQ
    @5
    @35
    @24
    @51
    symgov
    @2
    @17
    @50
    @16
    cQ
    @5
    @35
    @24
    @51
    symgcl
    eqeltrrd
    syl2anc
    wph
    cN
    @1
    cfv
    #
    cN
    @0
    cfv
    #
    cP
    cfv
    #
    c1
    cP
    cfv
    #
    cI
    wph
    @0
    wfun
    #
    cN
    @0
    cdm
    #
    wcel
    @60
    @62
    wceq
    wph
    @2
    @2
    cS
    wf1o
    #
    @2
    @2
    cS
    wf1
    #
    @64
    wph
    @39
    @66
    @43
    @2
    @17
    cS
    @16
    @35
    @24
    symgbasf1o
    syl
    #
    @2
    @2
    cS
    f1of1
    @67
    @2
    @2
    cS
    wf
    @64
    @2
    @2
    cS
    df-f1
    simprbi
    3syl
    wph
    cN
    @2
    @65
    @42
    wph
    @66
    @2
    @2
    @0
    wf1o
    @65
    @2
    wceq
    @68
    @2
    @2
    cS
    f1ocnv
    @2
    @2
    @0
    f1odm
    3syl
    eleqtrrd
    cN
    cP
    @0
    fvco
    syl2anc
    wph
    @61
    c1
    cP
    wph
    @40
    @61
    c1
    wceq
    @42
    @17
    @2
    cS
    vi
    @16
    cN
    cN
    @34
    madjusmdetlem2.s
    @35
    @24
    fzto1stinvn
    syl
    fveq2d
    wph
    @33
    @63
    cI
    wceq
    madjusmdet.i
    @2
    cP
    vi
    cI
    cN
    @34
    madjusmdetlem2.p
    fzto1stfv1
    syl
    3eqtrd
    wph
    cN
    @6
    cfv
    #
    cN
    @5
    cfv
    #
    cQ
    cfv
    #
    c1
    cQ
    cfv
    #
    cJ
    wph
    @5
    wfun
    #
    cN
    @5
    cdm
    #
    wcel
    @69
    @71
    wceq
    wph
    @2
    @2
    cT
    wf1o
    #
    @2
    @2
    cT
    wf1
    #
    @73
    wph
    @57
    @75
    @58
    @2
    @17
    cT
    @16
    @35
    @24
    symgbasf1o
    syl
    #
    @2
    @2
    cT
    f1of1
    @76
    @2
    @2
    cT
    wf
    @73
    @2
    @2
    cT
    df-f1
    simprbi
    3syl
    wph
    cN
    @2
    @74
    @42
    wph
    @75
    @2
    @2
    @5
    wf1o
    @74
    @2
    wceq
    @77
    @2
    @2
    cT
    f1ocnv
    @2
    @2
    @5
    f1odm
    3syl
    eleqtrrd
    cN
    cQ
    @5
    fvco
    syl2anc
    wph
    @70
    c1
    cQ
    wph
    @40
    @70
    c1
    wceq
    @42
    @17
    @2
    cT
    vj
    @16
    cN
    cN
    @34
    madjusmdetlem4.t
    @35
    @24
    fzto1stinvn
    syl
    fveq2d
    wph
    @54
    @72
    cJ
    wceq
    madjusmdet.j
    @2
    cQ
    vj
    cJ
    cN
    @34
    madjusmdetlem4.q
    fzto1stfv1
    syl
    3eqtrd
    wph
    cA
    cB
    cD
    cP
    cQ
    cR
    cS
    cT
    c.x
    @15
    vi
    vj
    cE
    cI
    cJ
    cK
    cM
    cN
    @23
    cZ
    madjusmdet.b
    madjusmdet.a
    madjusmdet.d
    madjusmdet.k
    madjusmdet.t
    madjusmdet.z
    madjusmdet.e
    madjusmdet.n
    madjusmdet.r
    madjusmdet.i
    madjusmdet.j
    madjusmdet.m
    madjusmdetlem2.p
    madjusmdetlem2.s
    madjusmdetlem4.q
    madjusmdetlem4.t
    @30
    wph
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    @33
    @54
    @15
    cB
    wcel
    wph
    cR
    ccrg
    wcel
    @78
    madjusmdet.r
    cR
    crngring
    syl
    madjusmdet.m
    madjusmdet.i
    madjusmdet.j
    cA
    cB
    cR
    cI
    cJ
    cM
    @2
    madjusmdet.a
    madjusmdet.b
    minmar1cl
    syl22anc
    madjusmdetlem3
    madjusmdetlem1
    wph
    @9
    @14
    @10
    c.x
    wph
    @8
    @13
    cZ
    wph
    @8
    @11
    cI
    c1
    caddc
    co
    #
    cexp
    co
    #
    @11
    cN
    c1
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @11
    cJ
    c1
    caddc
    co
    #
    cexp
    co
    #
    @82
    cmul
    co
    #
    cmul
    co
    #
    @13
    wph
    @4
    @83
    @7
    @86
    cmul
    wph
    @4
    cP
    @3
    cfv
    #
    @0
    @3
    cfv
    #
    cmul
    co
    #
    @83
    wph
    @46
    @31
    @32
    @4
    @90
    wceq
    @47
    @36
    @49
    @2
    @17
    @16
    cP
    @0
    @3
    @35
    @25
    @24
    psgnco
    syl3anc
    wph
    @88
    @80
    @89
    @82
    cmul
    wph
    @33
    @88
    @80
    wceq
    madjusmdet.i
    @17
    @2
    cP
    @3
    vi
    @16
    cI
    cN
    @34
    madjusmdetlem2.p
    @35
    @24
    @25
    psgnfzto1st
    syl
    wph
    @89
    cS
    @3
    cfv
    #
    @82
    wph
    @46
    @39
    @89
    @91
    wceq
    @47
    @43
    @2
    @17
    @16
    cS
    @3
    @35
    @25
    @24
    psgninv
    syl2anc
    wph
    @40
    @91
    @82
    wceq
    @42
    @17
    @2
    cS
    @3
    vi
    @16
    cN
    cN
    @34
    madjusmdetlem2.s
    @35
    @24
    @25
    psgnfzto1st
    syl
    eqtrd
    oveq12d
    eqtrd
    wph
    @7
    cQ
    @3
    cfv
    #
    @5
    @3
    cfv
    #
    cmul
    co
    #
    @86
    wph
    @46
    @52
    @53
    @7
    @94
    wceq
    @47
    @55
    @59
    @2
    @17
    @16
    cQ
    @5
    @3
    @35
    @25
    @24
    psgnco
    syl3anc
    wph
    @92
    @85
    @93
    @82
    cmul
    wph
    @54
    @92
    @85
    wceq
    madjusmdet.j
    @17
    @2
    cQ
    @3
    vj
    @16
    cJ
    cN
    @34
    madjusmdetlem4.q
    @35
    @24
    @25
    psgnfzto1st
    syl
    wph
    @93
    cT
    @3
    cfv
    #
    @82
    wph
    @46
    @57
    @93
    @95
    wceq
    @47
    @58
    @2
    @17
    @16
    cT
    @3
    @35
    @25
    @24
    psgninv
    syl2anc
    wph
    @40
    @95
    @82
    wceq
    @42
    @17
    @2
    cT
    @3
    vj
    @16
    cN
    cN
    @34
    madjusmdetlem4.t
    @35
    @24
    @25
    psgnfzto1st
    syl
    eqtrd
    oveq12d
    eqtrd
    oveq12d
    wph
    @87
    @80
    @85
    cmul
    co
    #
    @82
    @82
    cmul
    co
    #
    cmul
    co
    @13
    c1
    cmul
    co
    #
    @13
    wph
    @80
    @82
    @85
    @82
    wph
    @11
    @79
    wph
    c1
    wph
    1cnd
    #
    negcld
    #
    wph
    cI
    c1
    wph
    cI
    wph
    @2
    cn
    cI
    cN
    fz1ssnn
    #
    madjusmdet.i
    sseldi
    #
    nnnn0d
    #
    c1
    cn0
    wcel
    wph
    1nn0
    a1i
    #
    nn0addcld
    #
    expcld
    wph
    @11
    @81
    @100
    wph
    cN
    c1
    wph
    cN
    madjusmdet.n
    nnnn0d
    @104
    nn0addcld
    #
    expcld
    #
    wph
    @11
    @84
    @100
    wph
    cJ
    c1
    wph
    cJ
    wph
    @2
    cn
    cJ
    @101
    madjusmdet.j
    sseldi
    #
    nnnn0d
    #
    @104
    nn0addcld
    #
    expcld
    @107
    mul4d
    wph
    @96
    @13
    @97
    c1
    cmul
    wph
    @11
    @79
    @84
    caddc
    co
    #
    cexp
    co
    #
    @96
    @13
    wph
    @11
    @79
    @84
    @100
    @110
    @105
    expaddd
    wph
    @112
    @11
    @12
    c2
    caddc
    co
    #
    cexp
    co
    #
    @98
    @13
    wph
    @111
    @113
    @11
    cexp
    wph
    @111
    @12
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @113
    wph
    cI
    c1
    cJ
    c1
    wph
    cI
    @102
    nncnd
    @99
    wph
    cJ
    @108
    nncnd
    @99
    add4d
    @115
    c2
    @12
    caddc
    1p1e2
    oveq2i
    syl6eq
    oveq2d
    wph
    @114
    @13
    @11
    c2
    cexp
    co
    #
    cmul
    co
    @98
    wph
    @11
    @12
    c2
    @100
    c2
    cn0
    wcel
    wph
    2nn0
    a1i
    wph
    cI
    cJ
    @103
    @109
    nn0addcld
    #
    expaddd
    @116
    c1
    @13
    cmul
    neg1sqe1
    oveq2i
    syl6eq
    wph
    @13
    wph
    @11
    @12
    @100
    @117
    expcld
    mulid1d
    #
    3eqtrd
    eqtr3d
    wph
    @81
    cz
    wcel
    @82
    @11
    c1
    cpr
    wcel
    @97
    c1
    wceq
    wph
    @81
    @106
    nn0zd
    @81
    m1expcl2
    @82
    1neg1t1neg1
    3syl
    oveq12d
    @118
    3eqtrd
    eqtrd
    fveq2d
    oveq1d
    eqtrd
end
