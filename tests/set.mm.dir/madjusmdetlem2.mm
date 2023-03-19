include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "cif.mm"
include "ccnv.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "wf1o.mm"
include "csymg.mm"
include "cbs.mm"
include "cuz.mm"
include "cn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "syl.mm"
include "eqid.mm"
include "fzto1st.mm"
include "symgbasf1o.mm"
include "adantr.mm"
include "fznatpl1.mm"
include "sylan.mm"
include "wi.mm"
include "cv.mm"
include "cle.mm"
include "cmpt.mm"
include "eqeq1.mm"
include "breq1.mm"
include "oveq1.mm"
include "id.mm"
include "ifbieq12d.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "a1i.mm"
include "simpr.mm"
include "1red.mm"
include "crp.mm"
include "fz1ssnn.mm"
include "sseldi.mm"
include "nnrpd.mm"
include "ltaddrp2d.mm"
include "ltned.mm"
include "necomd.mm"
include "eqnetrd.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "elfzle2.mm"
include "nn0ltlem1.mm"
include "biimpar.mm"
include "syl21anc.mm"
include "nnltp1le.mm"
include "biimpa.mm"
include "eqbrtrd.mm"
include "iftrued.mm"
include "oveq1d.mm"
include "nncnd.mm"
include "1cnd.mm"
include "pncand.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "fvmptd.mm"
include "idi.mm"
include "f1ocnvfv.mm"
include "imp.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "breqtrrd.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "eqtr2d.mm"
include "wn.mm"
include "eqbrtrrd.mm"
include "ex.mm"
include "con3d.mm"
include "an32s.mm"
include "ifeqda.mm"
include "wfun.mm"
include "cdm.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "f1ofun.mm"
include "wss.mm"
include "csn.mm"
include "cdif.mm"
include "fzdif2.mm"
include "difss.mm"
include "syl6eqssr.mm"
include "f1odm.mm"
include "sseqtr4d.mm"
include "sseldd.mm"
include "fvco.mm"
include "syl2anc.mm"
include "eqtr4d.mm"

theorem madjusmdetlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vi: setvar i
  let cE: class E
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let cT: class T
  let cQ: class Q
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

  disjoint I i
  disjoint S i
  disjoint i ph
  disjoint B i
  disjoint I i
  disjoint J i
  disjoint M i
  disjoint N i
  disjoint P i
  disjoint R i
  disjoint i ph
  disjoint I x
  disjoint i x
  disjoint S j
  disjoint S k
  disjoint S l
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint T i
  disjoint T j
  disjoint T k
  disjoint T l
  disjoint X x
  disjoint N x
  disjoint ph x
  disjoint B j
  disjoint i j
  disjoint I j
  disjoint I k
  disjoint I l
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint J j
  disjoint J k
  disjoint J l
  disjoint M j
  disjoint M k
  disjoint M l
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint P j
  disjoint P k
  disjoint P l
  disjoint Q i
  disjoint Q j
  disjoint Q k
  disjoint Q l
  disjoint R j
  disjoint R k
  disjoint R l
  disjoint j ph
  assert |- ( ( ph /\ X e. ( 1 ... ( N - 1 ) ) ) -> if ( X < I , X , ( X + 1 ) ) = ( ( P o. `' S ) ` X ) )

  proof
    wph
    cX
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cX
    cI
    clt
    wbr
    #
    cX
    cX
    c1
    caddc
    co
    #
    cif
    cX
    cS
    ccnv
    #
    cfv
    #
    cP
    cfv
    #
    cX
    cP
    @6
    ccom
    cfv
    #
    @3
    @4
    cX
    @5
    @8
    @3
    @4
    wa
    #
    @8
    @5
    cP
    cfv
    #
    cX
    @3
    @8
    @11
    wceq
    #
    @4
    @3
    @7
    @5
    cP
    @3
    c1
    cN
    cfz
    co
    #
    @13
    cS
    wf1o
    #
    @5
    @13
    wcel
    #
    @5
    cS
    cfv
    cX
    wceq
    #
    @7
    @5
    wceq
    #
    wph
    @14
    @2
    wph
    cS
    @13
    csymg
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @14
    wph
    cN
    @13
    wcel
    #
    @20
    wph
    cN
    c1
    cuz
    cfv
    #
    wcel
    #
    @21
    wph
    cN
    cn
    @22
    madjusmdet.n
    nnuz
    syl6eleq
    #
    c1
    cN
    eluzfz2
    syl
    @19
    @13
    cS
    vi
    @18
    cN
    cN
    @13
    eqid
    madjusmdetlem2.s
    @18
    eqid
    #
    @19
    eqid
    #
    fzto1st
    syl
    #
    @13
    @19
    cS
    @18
    @25
    @26
    symgbasf1o
    #
    syl
    adantr
    wph
    cN
    cn
    wcel
    #
    @2
    @15
    madjusmdet.n
    cX
    cN
    fznatpl1
    sylan
    #
    @3
    @16
    wi
    @3
    vx
    @5
    vx
    cv
    #
    c1
    wceq
    #
    cN
    @31
    cN
    cle
    wbr
    #
    @31
    c1
    cmin
    co
    #
    @31
    cif
    #
    cif
    #
    cX
    @13
    cS
    @1
    cS
    vx
    @13
    @36
    cmpt
    #
    wceq
    @3
    cS
    vi
    @13
    vi
    cv
    #
    c1
    wceq
    #
    cN
    @38
    cN
    cle
    wbr
    #
    @38
    c1
    cmin
    co
    #
    @38
    cif
    #
    cif
    #
    cmpt
    @37
    madjusmdetlem2.s
    vi
    vx
    @13
    @43
    @36
    @38
    @31
    wceq
    #
    @39
    @32
    @42
    @35
    cN
    @38
    @31
    c1
    eqeq1
    #
    @44
    @40
    @33
    @41
    @38
    @34
    @31
    @38
    @31
    cN
    cle
    breq1
    @38
    @31
    c1
    cmin
    oveq1
    #
    @44
    id
    #
    ifbieq12d
    ifbieq2d
    cbvmptv
    eqtri
    a1i
    @3
    @31
    @5
    wceq
    #
    wa
    #
    @36
    @35
    @34
    cX
    @49
    @32
    cN
    @35
    @49
    @31
    c1
    @49
    @31
    @5
    c1
    @3
    @48
    simpr
    #
    @49
    c1
    @5
    @49
    c1
    @5
    @49
    1red
    #
    @49
    c1
    cX
    @51
    @3
    cX
    crp
    wcel
    @48
    @3
    cX
    @3
    @1
    cn
    cX
    @0
    fz1ssnn
    wph
    @2
    simpr
    #
    sseldi
    #
    nnrpd
    adantr
    ltaddrp2d
    #
    ltned
    necomd
    eqnetrd
    neneqd
    iffalsed
    @49
    @33
    @34
    @31
    @49
    @31
    @5
    cN
    cle
    @50
    @3
    @5
    cN
    cle
    wbr
    #
    @48
    @3
    cX
    cn
    wcel
    #
    @29
    cX
    cN
    clt
    wbr
    #
    @55
    @53
    wph
    @29
    @2
    madjusmdet.n
    adantr
    #
    @3
    cX
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    cX
    @0
    cle
    wbr
    #
    @57
    @3
    cX
    @53
    nnnn0d
    @3
    cN
    @58
    nnnn0d
    @3
    @2
    @61
    @52
    cX
    c1
    @0
    elfzle2
    syl
    @59
    @60
    wa
    @57
    @61
    cX
    cN
    nn0ltlem1
    biimpar
    syl21anc
    @56
    @29
    wa
    @57
    @55
    cX
    cN
    nnltp1le
    biimpa
    syl21anc
    adantr
    eqbrtrd
    iftrued
    @49
    @34
    @5
    c1
    cmin
    co
    #
    cX
    @49
    @31
    @5
    c1
    cmin
    @50
    oveq1d
    @3
    @62
    cX
    wceq
    @48
    @3
    cX
    c1
    @3
    cX
    @53
    nncnd
    @3
    1cnd
    pncand
    adantr
    eqtrd
    #
    3eqtrd
    @30
    @52
    fvmptd
    idi
    @14
    @15
    wa
    @16
    @17
    @13
    @13
    @5
    cX
    cS
    f1ocnvfv
    imp
    syl21anc
    fveq2d
    #
    adantr
    @10
    vx
    @5
    @32
    cI
    @31
    cI
    cle
    wbr
    #
    @34
    @31
    cif
    #
    cif
    #
    cX
    @13
    cP
    @1
    cP
    vx
    @13
    @67
    cmpt
    #
    wceq
    #
    @10
    cP
    vi
    @13
    @39
    cI
    @38
    cI
    cle
    wbr
    #
    @41
    @38
    cif
    #
    cif
    #
    cmpt
    @68
    madjusmdetlem2.p
    vi
    vx
    @13
    @72
    @67
    @44
    @39
    @32
    @71
    @66
    cI
    @45
    @44
    @70
    @65
    @41
    @38
    @34
    @31
    @44
    @38
    @31
    cI
    cle
    @47
    breq1d
    @46
    @47
    ifbieq12d
    ifbieq2d
    cbvmptv
    eqtri
    #
    a1i
    @10
    @48
    wa
    #
    @67
    @66
    @34
    cX
    @3
    @48
    @67
    @66
    wceq
    #
    @4
    @49
    @32
    cI
    @66
    @49
    @31
    c1
    @49
    c1
    @31
    @49
    c1
    @31
    @51
    @49
    c1
    @5
    @31
    clt
    @54
    @50
    breqtrrd
    ltned
    necomd
    neneqd
    iffalsed
    #
    adantlr
    @74
    @65
    @34
    @31
    @74
    @31
    @5
    cI
    cle
    @10
    @48
    simpr
    @74
    @56
    cI
    cn
    wcel
    #
    @4
    @5
    cI
    cle
    wbr
    #
    @3
    @56
    @4
    @48
    @53
    ad2antrr
    wph
    @77
    @2
    @4
    @48
    wph
    @13
    cn
    cI
    cN
    fz1ssnn
    madjusmdet.i
    sseldi
    #
    ad3antrrr
    @3
    @4
    @48
    simplr
    @56
    @77
    wa
    #
    @4
    @78
    cX
    cI
    nnltp1le
    #
    biimpa
    syl21anc
    eqbrtrd
    iftrued
    @3
    @48
    @34
    cX
    wceq
    @4
    @63
    adantlr
    3eqtrd
    @3
    @15
    @4
    @30
    adantr
    wph
    @2
    @4
    simplr
    fvmptd
    eqtr2d
    @3
    @4
    wn
    #
    wa
    #
    @8
    @11
    @5
    @3
    @12
    @82
    @64
    adantr
    @83
    vx
    @5
    @67
    @5
    @13
    cP
    @13
    @69
    @83
    @73
    a1i
    @83
    @48
    wa
    #
    @67
    @66
    @5
    @3
    @48
    @75
    @82
    @76
    adantlr
    @84
    @66
    @31
    @5
    @84
    @65
    @34
    @31
    @3
    @48
    @82
    @65
    wn
    #
    @49
    @82
    @85
    @49
    @65
    @4
    @49
    @65
    @4
    @49
    @65
    wa
    #
    @56
    @77
    @78
    @4
    @3
    @56
    @48
    @65
    @53
    ad2antrr
    wph
    @77
    @2
    @48
    @65
    @79
    ad3antrrr
    @86
    @31
    @5
    cI
    cle
    @49
    @48
    @65
    @50
    adantr
    @49
    @65
    simpr
    eqbrtrrd
    @80
    @4
    @78
    @81
    biimpar
    syl21anc
    ex
    con3d
    imp
    an32s
    iffalsed
    @83
    @48
    simpr
    eqtrd
    eqtrd
    @3
    @15
    @82
    @30
    adantr
    #
    @87
    fvmptd
    eqtr2d
    ifeqda
    @3
    @6
    wfun
    #
    cX
    @6
    cdm
    #
    wcel
    @9
    @8
    wceq
    wph
    @88
    @2
    wph
    @13
    @13
    @6
    wf1o
    #
    @88
    wph
    @20
    @14
    @90
    @27
    @28
    @13
    @13
    cS
    f1ocnv
    3syl
    #
    @13
    @13
    @6
    f1ofun
    syl
    adantr
    @3
    @1
    @89
    cX
    wph
    @1
    @89
    wss
    @2
    wph
    @1
    @13
    @89
    wph
    @1
    @13
    cN
    csn
    #
    cdif
    #
    @13
    wph
    @23
    @93
    @1
    wceq
    @24
    c1
    cN
    fzdif2
    syl
    @13
    @92
    difss
    syl6eqssr
    wph
    @90
    @89
    @13
    wceq
    @91
    @13
    @13
    @6
    f1odm
    syl
    sseqtr4d
    adantr
    @52
    sseldd
    cX
    cP
    @6
    fvco
    syl2anc
    eqtr4d
end
