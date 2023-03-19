include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cn0.mm"
include "w3a.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "cdecpmat.mm"
include "cco1.mm"
include "cv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cc0.mm"
include "cfz.mm"
include "cmin.mm"
include "wceq.mm"
include "simpr.mm"
include "3ad2ant1.mm"
include "pmatring.mm"
include "adantr.mm"
include "simpl.mm"
include "adantl.mm"
include "eqid.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "3adant3.mm"
include "simp33.mm"
include "3simpa.mm"
include "3ad2ant3.mm"
include "decpmate.mm"
include "syl31anc.mm"
include "cotp.mm"
include "cmmul.mm"
include "ply1ring.mm"
include "matmulr.mm"
include "eqcomd.mm"
include "sylan2.mm"
include "oveqd.mm"
include "cbs.mm"
include "cxp.mm"
include "cmap.mm"
include "wi.mm"
include "matbas2.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "impcom.mm"
include "simp31.mm"
include "simp32.mm"
include "mamufv.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "simpl2l.mm"
include "matecld.mm"
include "simpl2r.mm"
include "ralrimiva.mm"
include "coe1fzgsumd.mm"
include "cvv.mm"
include "simpl1r.mm"
include "coe1mul.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"

theorem decpmatmullem
  let vt: setvar t
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cU: class U
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cW: class W
  let vl: setvar l
  let vk: setvar k
  assume decpmatmul.p: |- P = ( Poly1 ` R )
  assume decpmatmul.c: |- C = ( N Mat P )
  assume decpmatmul.b: |- B = ( Base ` C )

  disjoint B t
  disjoint I l
  disjoint I t
  disjoint l t
  disjoint J l
  disjoint J t
  disjoint K l
  disjoint K t
  disjoint N t
  disjoint P t
  disjoint R l
  disjoint R t
  disjoint U l
  disjoint U t
  disjoint W l
  disjoint W t
  disjoint B k
  disjoint k t
  disjoint I k
  disjoint k l
  disjoint J k
  disjoint K k
  disjoint N k
  disjoint P k
  disjoint R k
  disjoint U k
  disjoint W k
  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( U e. B /\ W e. B ) /\ ( I e. N /\ J e. N /\ K e. NN0 ) ) -> ( I ( ( U ( .r ` C ) W ) decompPMat K ) J ) = ( R gsum ( t e. N |-> ( R gsum ( l e. ( 0 ... K ) |-> ( ( ( coe1 ` ( I U t ) ) ` l ) ( .r ` R ) ( ( coe1 ` ( t W J ) ) ` ( K - l ) ) ) ) ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cU
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    wa
    #
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    cK
    cn0
    wcel
    #
    w3a
    #
    w3a
    #
    cI
    cJ
    cU
    cW
    cC
    cmulr
    cfv
    #
    co
    #
    cK
    cdecpmat
    co
    co
    #
    cK
    cI
    cJ
    @12
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cK
    cP
    vt
    cN
    cI
    vt
    cv
    #
    cU
    co
    #
    @17
    cJ
    cW
    co
    #
    cP
    cmulr
    cfv
    #
    co
    #
    cmpt
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
    vt
    cN
    cR
    vl
    cc0
    cK
    cfz
    co
    #
    vl
    cv
    #
    @18
    cco1
    cfv
    cfv
    #
    cK
    @26
    cmin
    co
    #
    @19
    cco1
    cfv
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @10
    @1
    @12
    cB
    wcel
    #
    @8
    @6
    @7
    wa
    #
    @13
    @16
    wceq
    @2
    @5
    @1
    @9
    @0
    @1
    simpr
    3ad2ant1
    #
    @2
    @5
    @37
    @9
    @2
    @5
    wa
    cC
    crg
    wcel
    #
    @3
    @4
    @37
    @2
    @40
    @5
    cC
    cP
    cR
    cN
    decpmatmul.p
    decpmatmul.c
    pmatring
    adantr
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    @5
    @4
    @2
    @3
    @4
    simpr
    adantl
    cB
    cC
    @11
    cU
    cW
    decpmatmul.b
    @11
    eqid
    ringcl
    syl3anc
    3adant3
    @2
    @5
    @6
    @7
    @8
    simp33
    #
    @9
    @2
    @38
    @5
    @6
    @7
    @8
    3simpa
    3ad2ant3
    cB
    cC
    cP
    cR
    cI
    cJ
    cK
    @12
    cN
    crg
    decpmatmul.p
    decpmatmul.c
    decpmatmul.b
    decpmate
    syl31anc
    @10
    cK
    @15
    @23
    @10
    @14
    @22
    cco1
    @10
    @14
    cI
    cJ
    cU
    cW
    cP
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    co
    #
    co
    @22
    @10
    @12
    @43
    cI
    cJ
    @10
    @11
    @42
    cU
    cW
    @2
    @5
    @11
    @42
    wceq
    #
    @9
    @1
    @0
    cP
    crg
    wcel
    #
    @44
    cP
    cR
    decpmatmul.p
    ply1ring
    #
    @0
    @45
    wa
    #
    @42
    @11
    cC
    cP
    @42
    cN
    crg
    decpmatmul.c
    @42
    eqid
    #
    matmulr
    eqcomd
    sylan2
    3ad2ant1
    oveqd
    oveqd
    @10
    cP
    cbs
    cfv
    #
    cN
    cP
    @20
    vt
    @42
    cI
    cJ
    cN
    cN
    crg
    cU
    cW
    @48
    @49
    eqid
    #
    @20
    eqid
    #
    @2
    @5
    @45
    @9
    @1
    @45
    @0
    @46
    adantl
    3ad2ant1
    #
    @2
    @5
    @0
    @9
    @0
    @1
    simpl
    3ad2ant1
    #
    @53
    @53
    @2
    @5
    cU
    @49
    cN
    cN
    cxp
    cmap
    co
    #
    wcel
    #
    @9
    @5
    @2
    @55
    @3
    @2
    @55
    wi
    @4
    @2
    @3
    @55
    @2
    cB
    @54
    cU
    @1
    @0
    @45
    cB
    @54
    wceq
    @46
    @47
    @54
    cC
    cbs
    cfv
    #
    cB
    cC
    cP
    @49
    cN
    crg
    decpmatmul.c
    @50
    matbas2
    #
    decpmatmul.b
    syl6reqr
    sylan2
    eleq2d
    biimpcd
    adantr
    impcom
    3adant3
    @2
    @5
    cW
    @54
    wcel
    #
    @9
    @5
    @2
    @58
    @4
    @2
    @58
    wi
    @3
    @2
    @4
    @58
    @2
    cB
    @54
    cW
    @2
    @54
    @56
    cB
    @1
    @0
    @45
    @54
    @56
    wceq
    @46
    @57
    sylan2
    decpmatmul.b
    syl6reqr
    eleq2d
    biimpcd
    adantl
    impcom
    3adant3
    @2
    @5
    @6
    @7
    @8
    simp31
    #
    @2
    @5
    @6
    @7
    @8
    simp32
    #
    mamufv
    eqtrd
    fveq2d
    fveq1d
    @10
    @24
    cR
    vt
    cN
    cK
    @21
    cco1
    cfv
    #
    cfv
    #
    cmpt
    #
    cgsu
    co
    @36
    @10
    vt
    @49
    cP
    cR
    cK
    @21
    cN
    decpmatmul.p
    @50
    @39
    @41
    @10
    @21
    @49
    wcel
    #
    vt
    cN
    @10
    @17
    cN
    wcel
    #
    wa
    #
    @45
    @18
    @49
    wcel
    #
    @19
    @49
    wcel
    #
    @64
    @10
    @45
    @65
    @52
    adantr
    @66
    cC
    cB
    cP
    cI
    @17
    @49
    cU
    cN
    decpmatmul.c
    @50
    decpmatmul.b
    @10
    @6
    @65
    @59
    adantr
    @10
    @65
    simpr
    #
    @3
    @4
    @2
    @9
    @65
    simpl2l
    matecld
    #
    @66
    cC
    cB
    cP
    @17
    cJ
    @49
    cW
    cN
    decpmatmul.c
    @50
    decpmatmul.b
    @69
    @10
    @7
    @65
    @60
    adantr
    @3
    @4
    @2
    @9
    @65
    simpl2r
    matecld
    #
    @49
    cP
    @20
    @18
    @19
    @50
    @51
    ringcl
    syl3anc
    ralrimiva
    @53
    coe1fzgsumd
    @10
    @63
    @35
    cR
    cgsu
    @10
    vt
    cN
    @62
    @34
    @66
    vk
    cK
    cR
    vl
    cc0
    vk
    cv
    #
    cfz
    co
    #
    @27
    @72
    @26
    cmin
    co
    #
    @29
    cfv
    #
    @31
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @34
    cn0
    @61
    cvv
    @66
    @1
    @67
    @68
    @61
    vk
    cn0
    @78
    cmpt
    wceq
    @0
    @1
    @5
    @9
    @65
    simpl1r
    @70
    @71
    vl
    @49
    cR
    @20
    @31
    vk
    @18
    @19
    cP
    decpmatmul.p
    @51
    @31
    eqid
    @50
    coe1mul
    syl3anc
    @72
    cK
    wceq
    #
    @78
    @34
    wceq
    @66
    @79
    @77
    @33
    cR
    cgsu
    @79
    vl
    @73
    @76
    @25
    @32
    @72
    cK
    cc0
    cfz
    oveq2
    @79
    @75
    @30
    @27
    @31
    @79
    @74
    @28
    @29
    @72
    cK
    @26
    cmin
    oveq1
    fveq2d
    oveq2d
    mpteq12dv
    oveq2d
    adantl
    @10
    @8
    @65
    @41
    adantr
    @66
    cR
    @33
    cgsu
    ovexd
    fvmptd
    mpteq2dva
    oveq2d
    eqtrd
    3eqtrd
end
