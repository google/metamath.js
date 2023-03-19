include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
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
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "fzfid.mm"
include "cc.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "recnd.mm"
include "ad2antrl.mm"
include "simprrl.mm"
include "ad2antrr.mm"
include "fveecn.mm"
include "sylancom.mm"
include "simprrr.mm"
include "subcld.mm"
include "sqcld.mm"
include "fsummulc2.mm"
include "simprll.mm"
include "oveq1d.mm"
include "adantr.mm"
include "mulcld.mm"
include "fsumsub.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "simprlr.mm"
include "fsumadd.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "adantll.mm"
include "ax5seglem8.mm"
include "oveq1.mm"
include "eqcomd.mm"
include "sylan9eq.mm"
include "3impa.mm"
include "syl221anc.mm"
include "sumeq2dv.mm"

theorem ax5seglem9
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let vi: setvar i
  let vj: setvar j
  let cN: class N

  disjoint A i
  disjoint A j
  disjoint i j
  disjoint B i
  disjoint B j
  disjoint C i
  disjoint C j
  disjoint D i
  disjoint D j
  disjoint N i
  disjoint N j
  disjoint T i
  disjoint T j
  assert |- ( ( ( N e. NN /\ ( ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) ) /\ ( T e. ( 0 [,] 1 ) /\ A. i e. ( 1 ... N ) ( B ` i ) = ( ( ( 1 - T ) x. ( A ` i ) ) + ( T x. ( C ` i ) ) ) ) ) -> ( T x. sum_ j e. ( 1 ... N ) ( ( ( C ` j ) - ( D ` j ) ) ^ 2 ) ) = ( sum_ j e. ( 1 ... N ) ( ( ( B ` j ) - ( D ` j ) ) ^ 2 ) + ( ( 1 - T ) x. ( ( T x. sum_ j e. ( 1 ... N ) ( ( ( A ` j ) - ( C ` j ) ) ^ 2 ) ) - sum_ j e. ( 1 ... N ) ( ( ( A ` j ) - ( D ` j ) ) ^ 2 ) ) ) ) )

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
    wa
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    wa
    #
    wa
    wa
    #
    cT
    cc0
    c1
    cicc
    co
    wcel
    #
    vi
    cv
    #
    cB
    cfv
    #
    c1
    cT
    cmin
    co
    #
    @10
    cA
    cfv
    #
    cmul
    co
    #
    cT
    @10
    cC
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    wa
    #
    wa
    #
    cT
    @19
    vj
    cv
    #
    cC
    cfv
    #
    @23
    cD
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
    cmul
    co
    @19
    cT
    @27
    cmul
    co
    #
    vj
    csu
    #
    @19
    @23
    cB
    cfv
    #
    @25
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
    @12
    cT
    @19
    @23
    cA
    cfv
    #
    @24
    cmin
    co
    #
    c2
    cexp
    co
    #
    vj
    csu
    cmul
    co
    #
    @19
    @34
    @25
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
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @22
    @19
    @27
    cT
    vj
    @22
    c1
    cN
    fzfid
    #
    @9
    cT
    cc
    wcel
    #
    @8
    @20
    @9
    cT
    @9
    cT
    cr
    wcel
    cc0
    cT
    cle
    wbr
    cT
    c1
    cle
    wbr
    cc0
    c1
    cT
    0re
    1re
    elicc2i
    simp1bi
    recnd
    ad2antrl
    #
    @22
    @23
    @19
    wcel
    #
    wa
    #
    @26
    @48
    @24
    @25
    @22
    @47
    @5
    @24
    cc
    wcel
    #
    @8
    @5
    @21
    @47
    @0
    @4
    @5
    @6
    simprrl
    ad2antrr
    cC
    @23
    cN
    fveecn
    sylancom
    #
    @22
    @47
    @6
    @25
    cc
    wcel
    #
    @8
    @6
    @21
    @47
    @0
    @4
    @5
    @6
    simprrr
    ad2antrr
    cD
    @23
    cN
    fveecn
    sylancom
    #
    subcld
    sqcld
    fsummulc2
    @22
    @43
    @19
    @32
    @12
    cT
    @36
    cmul
    co
    #
    @39
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    vj
    csu
    #
    @29
    @22
    @43
    @33
    @19
    @55
    vj
    csu
    #
    caddc
    co
    @57
    @22
    @42
    @58
    @33
    caddc
    @22
    @42
    @12
    @19
    @54
    vj
    csu
    #
    cmul
    co
    @58
    @22
    @41
    @59
    @12
    cmul
    @22
    @41
    @19
    @53
    vj
    csu
    #
    @40
    cmin
    co
    @59
    @22
    @37
    @60
    @40
    cmin
    @22
    @19
    @36
    cT
    vj
    @44
    @46
    @48
    @35
    @48
    @34
    @24
    @22
    @47
    @2
    @34
    cc
    wcel
    #
    @8
    @2
    @21
    @47
    @0
    @2
    @3
    @7
    simprll
    ad2antrr
    cA
    @23
    cN
    fveecn
    sylancom
    #
    @50
    subcld
    sqcld
    #
    fsummulc2
    oveq1d
    @22
    @19
    @53
    @39
    vj
    @44
    @48
    cT
    @36
    @22
    @45
    @47
    @46
    adantr
    #
    @63
    mulcld
    #
    @48
    @38
    @48
    @34
    @25
    @62
    @52
    subcld
    sqcld
    #
    fsumsub
    eqtr4d
    oveq2d
    @22
    @19
    @54
    @12
    vj
    @44
    @22
    c1
    cc
    wcel
    #
    @45
    @12
    cc
    wcel
    #
    ax-1cn
    @46
    c1
    cT
    subcl
    #
    sylancr
    @48
    @53
    @39
    @65
    @66
    subcld
    #
    fsummulc2
    eqtrd
    oveq2d
    @22
    @19
    @32
    @55
    vj
    @44
    @48
    @31
    @48
    @30
    @25
    @22
    @47
    @3
    @30
    cc
    wcel
    @8
    @3
    @21
    @47
    @0
    @2
    @3
    @7
    simprlr
    ad2antrr
    cB
    @23
    cN
    fveecn
    sylancom
    @52
    subcld
    sqcld
    @48
    @12
    @54
    @48
    @67
    @45
    @68
    ax-1cn
    @64
    @69
    sylancr
    @70
    mulcld
    fsumadd
    eqtr4d
    @22
    @19
    @28
    @56
    vj
    @48
    @61
    @45
    @49
    @51
    @30
    @12
    @34
    cmul
    co
    #
    cT
    @24
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @28
    @56
    wceq
    #
    @62
    @64
    @50
    @52
    @21
    @47
    @74
    @8
    @20
    @47
    @74
    @9
    @18
    @74
    vi
    @23
    @19
    @10
    @23
    wceq
    #
    @11
    @30
    @17
    @73
    @10
    @23
    cB
    fveq2
    @76
    @14
    @71
    @16
    @72
    caddc
    @76
    @13
    @34
    @12
    cmul
    @10
    @23
    cA
    fveq2
    oveq2d
    @76
    @15
    @24
    cT
    cmul
    @10
    @23
    cC
    fveq2
    oveq2d
    oveq12d
    eqeq12d
    rspccva
    adantll
    adantll
    @61
    @45
    wa
    #
    @49
    @51
    wa
    #
    @74
    @75
    @77
    @78
    wa
    @74
    @28
    @73
    @25
    cmin
    co
    #
    c2
    cexp
    co
    #
    @55
    caddc
    co
    #
    @56
    @34
    @24
    @25
    cT
    ax5seglem8
    @74
    @56
    @81
    @74
    @32
    @80
    @55
    caddc
    @74
    @31
    @79
    c2
    cexp
    @30
    @73
    @25
    cmin
    oveq1
    oveq1d
    oveq1d
    eqcomd
    sylan9eq
    3impa
    syl221anc
    sumeq2dv
    eqtr4d
    eqtr4d
end
