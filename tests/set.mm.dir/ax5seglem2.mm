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
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cc.mm"
include "simpl2l.mm"
include "fveecn.mm"
include "sylancom.mm"
include "simpl2r.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "recnd.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "adantll.mm"
include "3ad2antl3.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "mpan.mm"
include "simp1.mm"
include "mulcld.mm"
include "simp3.mm"
include "simp2.mm"
include "addsubassd.mm"
include "subdi.mm"
include "syl3an1.mm"
include "3coml.mm"
include "subdir.mm"
include "mp3an1.mm"
include "ancoms.mm"
include "3adant1.mm"
include "mulid2.mm"
include "3ad2ant2.mm"
include "eqtrd.mm"
include "subsub2d.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "3adant3.mm"
include "sqmuld.mm"
include "sylan9eqr.mm"
include "syl31anc.mm"
include "sumeq2dv.mm"
include "fzfid.mm"
include "resubcl.mm"
include "sylancr.mm"
include "resqcld.mm"
include "3adant2r.mm"
include "3adant2l.mm"
include "subcld.mm"
include "sqcld.mm"
include "3expa.mm"
include "3adantl3.mm"
include "fsummulc2.mm"

theorem ax5seglem2
  let cA: class A
  let cB: class B
  let cC: class C
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
  disjoint N i
  disjoint N j
  disjoint T i
  disjoint T j
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( T e. ( 0 [,] 1 ) /\ A. i e. ( 1 ... N ) ( B ` i ) = ( ( ( 1 - T ) x. ( A ` i ) ) + ( T x. ( C ` i ) ) ) ) ) -> sum_ j e. ( 1 ... N ) ( ( ( B ` j ) - ( C ` j ) ) ^ 2 ) = ( ( ( 1 - T ) ^ 2 ) x. sum_ j e. ( 1 ... N ) ( ( ( A ` j ) - ( C ` j ) ) ^ 2 ) ) )

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
    cC
    @1
    wcel
    #
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
    @6
    cA
    cfv
    #
    cmul
    co
    #
    cT
    @6
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
    w3a
    #
    @15
    vj
    cv
    #
    cB
    cfv
    #
    @19
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
    @15
    @8
    c2
    cexp
    co
    #
    @19
    cA
    cfv
    #
    @21
    cmin
    co
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    vj
    csu
    @24
    @15
    @27
    vj
    csu
    cmul
    co
    @18
    @15
    @23
    @28
    vj
    @18
    @19
    @15
    wcel
    #
    wa
    @25
    cc
    wcel
    #
    @21
    cc
    wcel
    #
    cT
    cc
    wcel
    #
    @20
    @8
    @25
    cmul
    co
    #
    cT
    @21
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @23
    @28
    wceq
    @18
    @29
    @2
    @30
    @2
    @3
    @0
    @17
    @29
    simpl2l
    cA
    @19
    cN
    fveecn
    #
    sylancom
    @18
    @29
    @3
    @31
    @2
    @3
    @0
    @17
    @29
    simpl2r
    cC
    @19
    cN
    fveecn
    #
    sylancom
    @18
    @32
    @29
    @17
    @0
    @32
    @4
    @5
    @32
    @16
    @5
    cT
    @5
    cT
    cr
    wcel
    #
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
    #
    recnd
    adantr
    3ad2ant3
    adantr
    @17
    @0
    @29
    @36
    @4
    @16
    @29
    @36
    @5
    @14
    @36
    vi
    @19
    @15
    @6
    @19
    wceq
    #
    @7
    @20
    @13
    @35
    @6
    @19
    cB
    fveq2
    @41
    @10
    @33
    @12
    @34
    caddc
    @41
    @9
    @25
    @8
    cmul
    @6
    @19
    cA
    fveq2
    oveq2d
    @41
    @11
    @21
    cT
    cmul
    @6
    @19
    cC
    fveq2
    oveq2d
    oveq12d
    eqeq12d
    rspccva
    adantll
    3ad2antl3
    @36
    @30
    @31
    @32
    w3a
    #
    @23
    @35
    @21
    cmin
    co
    #
    c2
    cexp
    co
    #
    @28
    @36
    @22
    @43
    c2
    cexp
    @20
    @35
    @21
    cmin
    oveq1
    oveq1d
    @42
    @44
    @8
    @26
    cmul
    co
    #
    c2
    cexp
    co
    @28
    @42
    @43
    @45
    c2
    cexp
    @42
    @43
    @33
    @34
    @21
    cmin
    co
    caddc
    co
    #
    @45
    @42
    @33
    @34
    @21
    @42
    @8
    @25
    @32
    @30
    @8
    cc
    wcel
    #
    @31
    c1
    cc
    wcel
    #
    @32
    @47
    ax-1cn
    c1
    cT
    subcl
    mpan
    #
    3ad2ant3
    #
    @30
    @31
    @32
    simp1
    mulcld
    #
    @42
    cT
    @21
    @30
    @31
    @32
    simp3
    @30
    @31
    @32
    simp2
    #
    mulcld
    #
    @52
    addsubassd
    @42
    @45
    @33
    @8
    @21
    cmul
    co
    #
    cmin
    co
    #
    @33
    @21
    @34
    cmin
    co
    #
    cmin
    co
    @46
    @32
    @30
    @31
    @45
    @55
    wceq
    #
    @32
    @47
    @30
    @31
    @57
    @49
    @8
    @25
    @21
    subdi
    syl3an1
    3coml
    @42
    @54
    @56
    @33
    cmin
    @42
    @54
    c1
    @21
    cmul
    co
    #
    @34
    cmin
    co
    #
    @56
    @31
    @32
    @54
    @59
    wceq
    #
    @30
    @32
    @31
    @60
    @48
    @32
    @31
    @60
    ax-1cn
    c1
    cT
    @21
    subdir
    mp3an1
    ancoms
    3adant1
    @31
    @30
    @59
    @56
    wceq
    @32
    @31
    @58
    @21
    @34
    cmin
    @21
    mulid2
    oveq1d
    3ad2ant2
    eqtrd
    oveq2d
    @42
    @33
    @21
    @34
    @51
    @52
    @53
    subsub2d
    3eqtrd
    eqtr4d
    oveq1d
    @42
    @8
    @26
    @50
    @30
    @31
    @26
    cc
    wcel
    @32
    @25
    @21
    subcl
    3adant3
    sqmuld
    eqtrd
    sylan9eqr
    syl31anc
    sumeq2dv
    @18
    @15
    @27
    @24
    vj
    @18
    c1
    cN
    fzfid
    @17
    @0
    @24
    cc
    wcel
    #
    @4
    @5
    @61
    @16
    @5
    @24
    @5
    @8
    @5
    c1
    cr
    wcel
    @39
    @8
    cr
    wcel
    1re
    @40
    c1
    cT
    resubcl
    sylancr
    resqcld
    recnd
    adantr
    3ad2ant3
    @0
    @4
    @29
    @27
    cc
    wcel
    #
    @17
    @0
    @4
    @29
    @62
    @0
    @4
    @29
    w3a
    #
    @26
    @63
    @25
    @21
    @0
    @2
    @29
    @30
    @3
    @2
    @29
    @30
    @0
    @37
    3adant1
    3adant2r
    @0
    @3
    @29
    @31
    @2
    @3
    @29
    @31
    @0
    @38
    3adant1
    3adant2l
    subcld
    sqcld
    3expa
    3adantl3
    fsummulc2
    eqtr4d
end
