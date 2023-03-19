include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cr.mm"
include "cc.mm"
include "simp22l.mm"
include "cle.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "resqcl.mm"
include "recnd.mm"
include "3syl.mm"
include "simp22r.mm"
include "fzfid.mm"
include "simprl1.mm"
include "3ad2ant1.mm"
include "fveecn.mm"
include "sylan.mm"
include "simprl3.mm"
include "subcld.mm"
include "sqcld.mm"
include "fsumcl.mm"
include "simp1l.mm"
include "simp1rl.mm"
include "simp21.mm"
include "simp23l.mm"
include "ax5seglem5.mm"
include "syl23anc.mm"
include "simp3l.mm"
include "wb.mm"
include "simprl2.mm"
include "simprr1.mm"
include "simprr2.mm"
include "brcgr.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "ax5seglem1.mm"
include "syl122anc.mm"
include "simprr3.mm"
include "simp23r.mm"
include "3eqtr3d.mm"
include "simp1rr.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3r.mm"
include "ax5seglem3.mm"
include "syl322anc.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "mulcan2ad.mm"
include "simp2bi.mm"
include "jca.mm"
include "syl.mm"
include "sq11.mm"
include "syl2anc.mm"

theorem ax5seglem6
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cN: class N
  let vj: setvar j

  disjoint A i
  disjoint B i
  disjoint C i
  disjoint D i
  disjoint E i
  disjoint F i
  disjoint N i
  disjoint S i
  disjoint T i
  disjoint A j
  disjoint i j
  disjoint B j
  disjoint C j
  disjoint D j
  disjoint E j
  disjoint F j
  disjoint N j
  disjoint S j
  disjoint T j
  assert |- ( ( ( N e. NN /\ ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) ) /\ ( A =/= B /\ ( T e. ( 0 [,] 1 ) /\ S e. ( 0 [,] 1 ) ) /\ ( A. i e. ( 1 ... N ) ( B ` i ) = ( ( ( 1 - T ) x. ( A ` i ) ) + ( T x. ( C ` i ) ) ) /\ A. i e. ( 1 ... N ) ( E ` i ) = ( ( ( 1 - S ) x. ( D ` i ) ) + ( S x. ( F ` i ) ) ) ) ) /\ ( <. A , B >. Cgr <. D , E >. /\ <. B , C >. Cgr <. E , F >. ) ) -> T = S )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    #
    cD
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    cF
    @1
    wcel
    #
    w3a
    #
    wa
    #
    wa
    #
    cA
    cB
    wne
    #
    cT
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    cS
    @13
    wcel
    #
    wa
    #
    vi
    cv
    #
    cB
    cfv
    c1
    cT
    cmin
    co
    @17
    cA
    cfv
    cmul
    co
    cT
    @17
    cC
    cfv
    cmul
    co
    caddc
    co
    wceq
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    @17
    cE
    cfv
    c1
    cS
    cmin
    co
    @17
    cD
    cfv
    cmul
    co
    cS
    @17
    cF
    cfv
    cmul
    co
    caddc
    co
    wceq
    vi
    @18
    wral
    #
    wa
    #
    w3a
    #
    cA
    cB
    cop
    cD
    cE
    cop
    ccgr
    wbr
    #
    cB
    cC
    cop
    cE
    cF
    cop
    ccgr
    wbr
    #
    wa
    #
    w3a
    #
    cT
    c2
    cexp
    co
    #
    cS
    c2
    cexp
    co
    #
    wceq
    #
    cT
    cS
    wceq
    #
    @26
    @27
    @28
    @18
    vj
    cv
    #
    cA
    cfv
    #
    @31
    cC
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vj
    csu
    #
    @26
    @14
    cT
    cr
    wcel
    #
    @27
    cc
    wcel
    @14
    @15
    @12
    @21
    @11
    @25
    simp22l
    #
    @14
    @37
    cc0
    cT
    cle
    wbr
    #
    cT
    c1
    cle
    wbr
    #
    cc0
    c1
    cT
    0re
    1re
    elicc2i
    #
    simp1bi
    #
    @37
    @27
    cT
    resqcl
    recnd
    3syl
    @26
    @15
    cS
    cr
    wcel
    #
    @28
    cc
    wcel
    @14
    @15
    @12
    @21
    @11
    @25
    simp22r
    #
    @15
    @43
    cc0
    cS
    cle
    wbr
    #
    cS
    c1
    cle
    wbr
    #
    cc0
    c1
    cS
    0re
    1re
    elicc2i
    #
    simp1bi
    #
    @43
    @28
    cS
    resqcl
    recnd
    3syl
    @26
    @18
    @35
    vj
    @26
    c1
    cN
    fzfid
    @26
    @31
    @18
    wcel
    #
    wa
    #
    @34
    @50
    @32
    @33
    @26
    @2
    @49
    @32
    cc
    wcel
    @11
    @22
    @2
    @25
    @2
    @3
    @4
    @9
    @0
    simprl1
    #
    3ad2ant1
    #
    cA
    @31
    cN
    fveecn
    sylan
    @26
    @4
    @49
    @33
    cc
    wcel
    @11
    @22
    @4
    @25
    @2
    @3
    @4
    @9
    @0
    simprl3
    3ad2ant1
    #
    cC
    @31
    cN
    fveecn
    sylan
    subcld
    sqcld
    fsumcl
    @26
    @0
    @5
    @12
    @14
    @19
    @36
    cc0
    wne
    @0
    @10
    @22
    @25
    simp1l
    #
    @5
    @9
    @0
    @22
    @25
    simp1rl
    #
    @11
    @12
    @16
    @21
    @25
    simp21
    @38
    @19
    @20
    @12
    @16
    @11
    @25
    simp23l
    #
    cA
    cB
    cC
    cT
    vi
    vj
    cN
    ax5seglem5
    syl23anc
    @26
    @27
    @36
    cmul
    co
    #
    @28
    @18
    @31
    cD
    cfv
    #
    @31
    cF
    cfv
    cmin
    co
    c2
    cexp
    co
    vj
    csu
    #
    cmul
    co
    #
    @28
    @36
    cmul
    co
    @26
    @18
    @32
    @31
    cB
    cfv
    cmin
    co
    c2
    cexp
    co
    vj
    csu
    #
    @18
    @58
    @31
    cE
    cfv
    cmin
    co
    c2
    cexp
    co
    vj
    csu
    #
    @57
    @60
    @26
    @23
    @61
    @62
    wceq
    #
    @11
    @22
    @23
    @24
    simp3l
    #
    @11
    @22
    @23
    @63
    wb
    #
    @25
    @11
    @2
    @3
    @6
    @7
    @65
    @51
    @2
    @3
    @4
    @9
    @0
    simprl2
    @6
    @7
    @8
    @5
    @0
    simprr1
    #
    @6
    @7
    @8
    @5
    @0
    simprr2
    cA
    cB
    cD
    cE
    vj
    cN
    brcgr
    syl22anc
    3ad2ant1
    mpbid
    @26
    @0
    @2
    @4
    @14
    @19
    @61
    @57
    wceq
    @54
    @52
    @53
    @38
    @56
    cA
    cB
    cC
    cT
    vi
    vj
    cN
    ax5seglem1
    syl122anc
    @26
    @0
    @6
    @8
    @15
    @20
    @62
    @60
    wceq
    @54
    @11
    @22
    @6
    @25
    @66
    3ad2ant1
    @11
    @22
    @8
    @25
    @6
    @7
    @8
    @5
    @0
    simprr3
    3ad2ant1
    @44
    @19
    @20
    @12
    @16
    @11
    @25
    simp23r
    cD
    cE
    cF
    cS
    vi
    vj
    cN
    ax5seglem1
    syl122anc
    3eqtr3d
    @26
    @36
    @59
    @28
    cmul
    @26
    @0
    @5
    @9
    @16
    @21
    @23
    @24
    @36
    @59
    wceq
    @54
    @55
    @5
    @9
    @0
    @22
    @25
    simp1rr
    @11
    @12
    @16
    @21
    @25
    simp22
    @11
    @12
    @16
    @21
    @25
    simp23
    @64
    @11
    @22
    @23
    @24
    simp3r
    cA
    cB
    cC
    cD
    cS
    cT
    vi
    vj
    cE
    cF
    cN
    ax5seglem3
    syl322anc
    oveq2d
    eqtr4d
    mulcan2ad
    @26
    @37
    @39
    wa
    #
    @43
    @45
    wa
    #
    @29
    @30
    wb
    @26
    @14
    @67
    @38
    @14
    @37
    @39
    @42
    @14
    @37
    @39
    @40
    @41
    simp2bi
    jca
    syl
    @26
    @15
    @68
    @44
    @15
    @43
    @45
    @48
    @15
    @43
    @45
    @46
    @47
    simp2bi
    jca
    syl
    cT
    cS
    sq11
    syl2anc
    mpbid
end
