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
include "adantr.mm"
include "3ad2ant3.mm"
include "recnd.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "adantll.mm"
include "3ad2antl3.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "subdi.mm"
include "3coml.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "mpan.mm"
include "adantl.mm"
include "simpl.mm"
include "subdir.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "nncan.mm"
include "mulid2.mm"
include "3eqtr3rd.mm"
include "3adant2.mm"
include "simp1.mm"
include "mulcl.mm"
include "sylan.mm"
include "ancoms.mm"
include "3adant1.mm"
include "subsub4d.mm"
include "3eqtr2rd.mm"
include "simp3.mm"
include "3adant3.mm"
include "sqmuld.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "syl31anc.mm"
include "sumeq2dv.mm"
include "fzfid.mm"
include "resqcld.mm"
include "3adant2r.mm"
include "3adant2l.mm"
include "sqcld.mm"
include "3expa.mm"
include "3adantl3.mm"
include "fsummulc2.mm"
include "eqtr4d.mm"

theorem ax5seglem1
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
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( T e. ( 0 [,] 1 ) /\ A. i e. ( 1 ... N ) ( B ` i ) = ( ( ( 1 - T ) x. ( A ` i ) ) + ( T x. ( C ` i ) ) ) ) ) -> sum_ j e. ( 1 ... N ) ( ( ( A ` j ) - ( B ` j ) ) ^ 2 ) = ( ( T ^ 2 ) x. sum_ j e. ( 1 ... N ) ( ( ( A ` j ) - ( C ` j ) ) ^ 2 ) ) )

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
    cA
    cfv
    #
    @19
    cB
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
    cT
    c2
    cexp
    co
    #
    @20
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
    @20
    cc
    wcel
    #
    @25
    cc
    wcel
    #
    cT
    cc
    wcel
    #
    @21
    @8
    @20
    cmul
    co
    #
    cT
    @25
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
    @18
    cT
    @17
    @0
    cT
    cr
    wcel
    #
    @4
    @5
    @39
    @16
    @5
    @39
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
    adantr
    3ad2ant3
    recnd
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
    @21
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
    @20
    @8
    cmul
    @6
    @19
    cA
    fveq2
    oveq2d
    @41
    @11
    @25
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
    @20
    @35
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
    @21
    @35
    @20
    cmin
    oveq2
    oveq1d
    @42
    @44
    cT
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
    @45
    cT
    @20
    cmul
    co
    #
    @34
    cmin
    co
    #
    @20
    @33
    cmin
    co
    #
    @34
    cmin
    co
    #
    @43
    @32
    @30
    @31
    @45
    @47
    wceq
    cT
    @20
    @25
    subdi
    3coml
    @30
    @32
    @49
    @47
    wceq
    @31
    @30
    @32
    wa
    #
    @48
    @46
    @34
    cmin
    @50
    c1
    @8
    cmin
    co
    #
    @20
    cmul
    co
    #
    c1
    @20
    cmul
    co
    #
    @33
    cmin
    co
    #
    @46
    @48
    @50
    @8
    cc
    wcel
    #
    @30
    @52
    @54
    wceq
    #
    @32
    @55
    @30
    c1
    cc
    wcel
    #
    @32
    @55
    ax-1cn
    c1
    cT
    subcl
    mpan
    #
    adantl
    @30
    @32
    simpl
    @57
    @55
    @30
    @56
    ax-1cn
    c1
    @8
    @20
    subdir
    mp3an1
    syl2anc
    @32
    @52
    @46
    wceq
    @30
    @32
    @51
    cT
    @20
    cmul
    @57
    @32
    @51
    cT
    wceq
    ax-1cn
    c1
    cT
    nncan
    mpan
    oveq1d
    adantl
    @30
    @54
    @48
    wceq
    @32
    @30
    @53
    @20
    @33
    cmin
    @20
    mulid2
    oveq1d
    adantr
    3eqtr3rd
    oveq1d
    3adant2
    @42
    @20
    @33
    @34
    @30
    @31
    @32
    simp1
    @30
    @32
    @33
    cc
    wcel
    #
    @31
    @32
    @30
    @59
    @32
    @55
    @30
    @59
    @58
    @8
    @20
    mulcl
    sylan
    ancoms
    3adant2
    @31
    @32
    @34
    cc
    wcel
    #
    @30
    @32
    @31
    @60
    cT
    @25
    mulcl
    ancoms
    3adant1
    subsub4d
    3eqtr2rd
    oveq1d
    @42
    cT
    @26
    @30
    @31
    @32
    simp3
    @30
    @31
    @26
    cc
    wcel
    #
    @32
    @20
    @25
    subcl
    #
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
    @63
    @16
    @5
    @24
    @5
    cT
    @40
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
    @64
    @0
    @4
    @29
    w3a
    #
    @26
    @65
    @30
    @31
    @61
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
    @62
    syl2anc
    sqcld
    3expa
    3adantl3
    fsummulc2
    eqtr4d
end
