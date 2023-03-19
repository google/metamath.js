include "csmat.mm"
include "cfv.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "ccom.mm"
include "cvv.mm"
include "wss.mm"
include "csn.mm"
include "cdif.mm"
include "cuz.mm"
include "cn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "fzdif2.mm"
include "syl.mm"
include "difss.mm"
include "syl6eqssr.mm"
include "adantr.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "ovexd.mm"
include "ovmpt4g.mm"
include "syl3anc.mm"
include "ovresd.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "cif.mm"
include "cbs.mm"
include "eqid.mm"
include "cmap.mm"
include "matbas2i.mm"
include "fz1ssnn.mm"
include "sseldi.mm"
include "eqidd.mm"
include "smatlem.mm"
include "madjusmdetlem2.mm"
include "syldan.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"
include "ralrimivva.mm"
include "cmat.mm"
include "wb.mm"
include "smatcl.mm"
include "cmpt2.mm"
include "ccrg.mm"
include "fzfid.mm"
include "w3a.mm"
include "csymg.mm"
include "fzto1st.mm"
include "cminusg.mm"
include "eluzfz2.mm"
include "symginv.mm"
include "cgrp.mm"
include "cfn.mm"
include "symggrp.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "cplusg.mm"
include "symgov.mm"
include "symgcl.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "symgfv.mm"
include "simp3.mm"
include "matecld.mm"
include "matbas2d.mm"
include "syl5eqel.mm"
include "submatres.mm"
include "eqmat.mm"
include "mpbird.mm"
include "eqtr4d.mm"

theorem madjusmdetlem3
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
  let cU: class U
  let vi: setvar i
  let vj: setvar j
  let cE: class E
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
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
  assume madjusmdetlem3.w: |- W = ( i e. ( 1 ... N ) , j e. ( 1 ... N ) |-> ( ( ( P o. `' S ) ` i ) U ( ( Q o. `' T ) ` j ) ) )
  assume madjusmdetlem3.u: |- ( ph -> U e. B )

  disjoint U i
  disjoint U j
  disjoint i j
  disjoint W i
  disjoint W j
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
  assert |- ( ph -> ( I ( subMat1 ` U ) J ) = ( N ( subMat1 ` W ) N ) )

  proof
    wph
    cI
    cJ
    cU
    csmat
    cfv
    co
    #
    cW
    c1
    cN
    c1
    cmin
    co
    cfz
    co
    #
    @1
    cxp
    cres
    #
    cN
    cN
    cW
    csmat
    cfv
    co
    #
    wph
    @0
    @2
    wceq
    #
    vi
    cv
    #
    vj
    cv
    #
    @0
    co
    #
    @5
    @6
    @2
    co
    #
    wceq
    #
    vj
    @1
    wral
    vi
    @1
    wral
    #
    wph
    @9
    vi
    vj
    @1
    @1
    wph
    @5
    @1
    wcel
    #
    @6
    @1
    wcel
    #
    wa
    #
    wa
    #
    @5
    @6
    cW
    co
    #
    @5
    cP
    cS
    ccnv
    #
    ccom
    #
    cfv
    #
    @6
    cQ
    cT
    ccnv
    #
    ccom
    #
    cfv
    #
    cU
    co
    #
    @8
    @7
    @14
    @5
    c1
    cN
    cfz
    co
    #
    wcel
    #
    @6
    @23
    wcel
    #
    @22
    cvv
    wcel
    @15
    @22
    wceq
    @14
    @1
    @23
    @5
    wph
    @1
    @23
    wss
    @13
    wph
    @1
    @23
    cN
    csn
    #
    cdif
    #
    @23
    wph
    cN
    c1
    cuz
    cfv
    #
    wcel
    #
    @27
    @1
    wceq
    wph
    cN
    cn
    @28
    madjusmdet.n
    nnuz
    syl6eleq
    #
    c1
    cN
    fzdif2
    syl
    @23
    @26
    difss
    syl6eqssr
    adantr
    #
    wph
    @11
    @12
    simprl
    #
    sseldd
    #
    @14
    @1
    @23
    @6
    @31
    wph
    @11
    @12
    simprr
    #
    sseldd
    #
    @14
    @18
    @21
    cU
    ovexd
    vi
    vj
    @23
    @23
    @22
    cW
    cvv
    madjusmdetlem3.w
    ovmpt4g
    syl3anc
    @14
    @5
    @6
    cW
    @1
    @32
    @34
    ovresd
    @14
    @7
    @5
    cI
    clt
    wbr
    @5
    @5
    c1
    caddc
    co
    cif
    #
    @6
    cJ
    clt
    wbr
    @6
    @6
    c1
    caddc
    co
    cif
    #
    cU
    co
    @22
    @14
    cU
    cR
    cbs
    cfv
    #
    @0
    @5
    @6
    cI
    cJ
    cN
    cN
    @36
    @37
    @0
    eqid
    #
    wph
    cN
    cn
    wcel
    #
    @13
    madjusmdet.n
    adantr
    #
    @41
    wph
    cI
    @23
    wcel
    #
    @13
    madjusmdet.i
    adantr
    wph
    cJ
    @23
    wcel
    #
    @13
    madjusmdet.j
    adantr
    wph
    cU
    @38
    @23
    @23
    cxp
    cmap
    co
    wcel
    #
    @13
    wph
    cU
    cB
    wcel
    #
    @44
    madjusmdetlem3.u
    cA
    cB
    cR
    @38
    cU
    @23
    madjusmdet.a
    @38
    eqid
    #
    madjusmdet.b
    matbas2i
    syl
    adantr
    @14
    @23
    cn
    @5
    cN
    fz1ssnn
    #
    @33
    sseldi
    @14
    @23
    cn
    @6
    @47
    @35
    sseldi
    @14
    @36
    eqidd
    @14
    @37
    eqidd
    smatlem
    @14
    @36
    @18
    @37
    @21
    cU
    wph
    @13
    @11
    @36
    @18
    wceq
    @32
    wph
    cA
    cB
    cD
    cP
    cR
    cS
    c.x
    vi
    cE
    cI
    cI
    cK
    cM
    cN
    @5
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
    madjusmdet.i
    madjusmdet.m
    madjusmdetlem2.p
    madjusmdetlem2.s
    madjusmdetlem2
    syldan
    wph
    @13
    @12
    @37
    @21
    wceq
    @34
    wph
    cA
    cB
    cD
    cQ
    cR
    cT
    c.x
    vj
    cE
    cJ
    cJ
    cK
    cM
    cN
    @6
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
    madjusmdet.j
    madjusmdet.j
    madjusmdet.m
    madjusmdetlem4.q
    madjusmdetlem4.t
    madjusmdetlem2
    syldan
    oveq12d
    eqtrd
    3eqtr4rd
    ralrimivva
    wph
    @0
    @1
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    @2
    @49
    wcel
    @4
    @10
    wb
    wph
    cA
    cB
    @49
    cR
    @0
    cI
    cJ
    cU
    cN
    madjusmdet.a
    madjusmdet.b
    @49
    eqid
    #
    @39
    madjusmdet.n
    madjusmdet.i
    madjusmdet.j
    madjusmdetlem3.u
    smatcl
    wph
    @3
    @2
    @49
    wph
    @40
    cW
    cB
    wcel
    @3
    @2
    wceq
    madjusmdet.n
    wph
    cW
    vi
    vj
    @23
    @23
    @22
    cmpt2
    cB
    madjusmdetlem3.w
    wph
    vi
    vj
    cA
    cB
    @22
    cR
    @38
    @23
    ccrg
    madjusmdet.a
    @46
    madjusmdet.b
    wph
    c1
    cN
    fzfid
    #
    madjusmdet.r
    wph
    @24
    @25
    w3a
    #
    cA
    cB
    cR
    @18
    @21
    @38
    cU
    @23
    madjusmdet.a
    @46
    madjusmdet.b
    @52
    @17
    @23
    csymg
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @24
    @18
    @23
    wcel
    wph
    @24
    @55
    @25
    wph
    cP
    @54
    wcel
    #
    @16
    @54
    wcel
    #
    @55
    wph
    @42
    @56
    madjusmdet.i
    @54
    @23
    cP
    vi
    @53
    cI
    cN
    @23
    eqid
    #
    madjusmdetlem2.p
    @53
    eqid
    #
    @54
    eqid
    #
    fzto1st
    syl
    wph
    cS
    @53
    cminusg
    cfv
    #
    cfv
    #
    @16
    @54
    wph
    cS
    @54
    wcel
    #
    @62
    @16
    wceq
    wph
    cN
    @23
    wcel
    #
    @63
    wph
    @29
    @64
    @30
    c1
    cN
    eluzfz2
    syl
    #
    @54
    @23
    cS
    vi
    @53
    cN
    cN
    @58
    madjusmdetlem2.s
    @59
    @60
    fzto1st
    syl
    #
    @23
    @54
    cS
    @53
    @61
    @59
    @60
    @61
    eqid
    #
    symginv
    syl
    wph
    @53
    cgrp
    wcel
    #
    @63
    @62
    @54
    wcel
    wph
    @23
    cfn
    wcel
    @68
    @51
    @23
    @53
    cfn
    @59
    symggrp
    syl
    #
    @66
    @54
    @53
    @61
    cS
    @60
    @67
    grpinvcl
    syl2anc
    eqeltrrd
    @56
    @57
    wa
    cP
    @16
    @53
    cplusg
    cfv
    #
    co
    @17
    @54
    @23
    @54
    @70
    @53
    cP
    @16
    @59
    @60
    @70
    eqid
    #
    symgov
    @23
    @54
    @70
    @53
    cP
    @16
    @59
    @60
    @71
    symgcl
    eqeltrrd
    syl2anc
    3ad2ant1
    wph
    @24
    @25
    simp2
    @23
    @54
    @17
    @53
    @5
    @59
    @60
    symgfv
    syl2anc
    @52
    @20
    @54
    wcel
    #
    @25
    @21
    @23
    wcel
    wph
    @24
    @72
    @25
    wph
    cQ
    @54
    wcel
    #
    @19
    @54
    wcel
    #
    @72
    wph
    @43
    @73
    madjusmdet.j
    @54
    @23
    cQ
    vj
    @53
    cJ
    cN
    @58
    madjusmdetlem4.q
    @59
    @60
    fzto1st
    syl
    wph
    cT
    @61
    cfv
    #
    @19
    @54
    wph
    cT
    @54
    wcel
    #
    @75
    @19
    wceq
    wph
    @64
    @76
    @65
    @54
    @23
    cT
    vj
    @53
    cN
    cN
    @58
    madjusmdetlem4.t
    @59
    @60
    fzto1st
    syl
    #
    @23
    @54
    cT
    @53
    @61
    @59
    @60
    @67
    symginv
    syl
    wph
    @68
    @76
    @75
    @54
    wcel
    @69
    @77
    @54
    @53
    @61
    cT
    @60
    @67
    grpinvcl
    syl2anc
    eqeltrrd
    @73
    @74
    wa
    cQ
    @19
    @70
    co
    @20
    @54
    @23
    @54
    @70
    @53
    cQ
    @19
    @59
    @60
    @71
    symgov
    @23
    @54
    @70
    @53
    cQ
    @19
    @59
    @60
    @71
    symgcl
    eqeltrrd
    syl2anc
    3ad2ant1
    wph
    @24
    @25
    simp3
    @23
    @54
    @20
    @53
    @6
    @59
    @60
    symgfv
    syl2anc
    wph
    @24
    @45
    @25
    madjusmdetlem3.u
    3ad2ant1
    matecld
    matbas2d
    syl5eqel
    #
    cA
    cB
    cR
    cW
    cN
    madjusmdet.a
    madjusmdet.b
    submatres
    syl2anc
    #
    wph
    cA
    cB
    @49
    cR
    @3
    cN
    cN
    cW
    cN
    madjusmdet.a
    madjusmdet.b
    @50
    @3
    eqid
    madjusmdet.n
    @65
    @65
    @78
    smatcl
    eqeltrrd
    @48
    @49
    cR
    vi
    vj
    @1
    @0
    @2
    @48
    eqid
    @50
    eqmat
    syl2anc
    mpbird
    @79
    eqtr4d
end
