include "wcel.mm"
include "cn.mm"
include "creps.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cv.mm"
include "csn.mm"
include "wex.mm"
include "ccsh.mm"
include "cc0.mm"
include "cfzo.mm"
include "wrex.mm"
include "cword.mm"
include "crab.mm"
include "wreu.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cn0.mm"
include "wb.mm"
include "nnnn0.mm"
include "repsdf2.mm"
include "sylan2.mm"
include "simp1.mm"
include "adantl.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "lbfzo0.mm"
include "biimpri.mm"
include "syl6bi.mm"
include "3ad2ant2.mm"
include "com12.mm"
include "imp.mm"
include "cshw0.mm"
include "syl.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "ex.mm"
include "sylbid.mm"
include "3impia.mm"
include "repsw.mm"
include "3adant3.mm"
include "simpll3.mm"
include "oveq1d.mm"
include "cz.mm"
include "ad2antrr.mm"
include "elfzoelz.mm"
include "repswcshw.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "biimpd.mm"
include "rexlimdva.mm"
include "ralrimiva.mm"
include "eqeq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "reu7.mm"
include "sylanbrc.mm"
include "reusn.mm"
include "sylib.mm"
include "eqeq1i.mm"
include "exbii.mm"
include "sylibr.mm"
include "cvv.mm"
include "cshwsex.mm"
include "3ad2ant1.mm"
include "hash1snb.mm"
include "mpbird.mm"

theorem cshwrepswhash1
  let vw: setvar w
  let cA: class A
  let vn: setvar n
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vu: setvar u
  let vr: setvar r
  assume cshwrepswhash1.m: |- M = { w e. Word V | E. n e. ( 0 ..^ ( # ` W ) ) ( W cyclShift n ) = w }

  disjoint V n
  disjoint V w
  disjoint n w
  disjoint W n
  disjoint W w
  disjoint A n
  disjoint A w
  disjoint N n
  disjoint N w
  disjoint A i
  disjoint A u
  disjoint i n
  disjoint i u
  disjoint i w
  disjoint n u
  disjoint u w
  disjoint M r
  disjoint N i
  disjoint N u
  disjoint V r
  disjoint V u
  disjoint n r
  disjoint r u
  disjoint r w
  disjoint W i
  disjoint W r
  disjoint W u
  disjoint i r
  assert |- ( ( A e. V /\ N e. NN /\ W = ( A repeatS N ) ) -> ( # ` M ) = 1 )

  proof
    cA
    cV
    wcel
    #
    cN
    cn
    wcel
    #
    cW
    cA
    cN
    creps
    co
    #
    wceq
    #
    w3a
    #
    cM
    chash
    cfv
    c1
    wceq
    #
    cM
    vr
    cv
    csn
    #
    wceq
    #
    vr
    wex
    #
    @4
    cW
    vn
    cv
    #
    ccsh
    co
    #
    vw
    cv
    #
    wceq
    #
    vn
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wrex
    #
    vw
    cV
    cword
    #
    crab
    #
    @6
    wceq
    #
    vr
    wex
    #
    @8
    @4
    @15
    vw
    @16
    wreu
    #
    @19
    @4
    @15
    vw
    @16
    wrex
    #
    @10
    vu
    cv
    #
    wceq
    #
    vn
    @14
    wrex
    #
    vw
    vu
    weq
    #
    wi
    #
    vu
    @16
    wral
    #
    vw
    @16
    wrex
    #
    @20
    @0
    @1
    @3
    @21
    @0
    @1
    wa
    #
    @3
    cW
    @16
    wcel
    #
    @13
    cN
    wceq
    #
    vi
    cv
    cW
    cfv
    cA
    wceq
    vi
    cc0
    cN
    cfzo
    co
    wral
    #
    w3a
    #
    @21
    @1
    @0
    cN
    cn0
    wcel
    #
    @3
    @33
    wb
    cN
    nnnn0
    #
    cA
    vi
    cN
    cV
    cW
    repsdf2
    sylan2
    #
    @29
    @33
    @21
    @29
    @33
    wa
    #
    @30
    @10
    cW
    wceq
    #
    vn
    @14
    wrex
    #
    @21
    @33
    @30
    @29
    @30
    @31
    @32
    simp1
    adantl
    #
    @37
    cc0
    @14
    wcel
    #
    cW
    cc0
    ccsh
    co
    #
    cW
    wceq
    #
    @39
    @29
    @33
    @41
    @1
    @33
    @41
    wi
    @0
    @33
    @1
    @41
    @31
    @30
    @1
    @41
    wi
    @32
    @31
    @1
    @13
    cn
    wcel
    #
    @41
    @1
    @44
    wb
    cN
    @13
    cN
    @13
    cn
    eleq1
    eqcoms
    @41
    @44
    @13
    lbfzo0
    biimpri
    syl6bi
    3ad2ant2
    com12
    adantl
    imp
    @37
    @30
    @43
    @40
    cV
    cW
    cshw0
    syl
    @38
    @43
    vn
    cc0
    @14
    @9
    cc0
    wceq
    @10
    @42
    cW
    @9
    cc0
    cW
    ccsh
    oveq2
    eqeq1d
    rspcev
    syl2anc
    @15
    @39
    vw
    cW
    @16
    @11
    cW
    wceq
    @12
    @38
    vn
    @14
    @11
    cW
    @10
    eqeq2
    rexbidv
    rspcev
    syl2anc
    ex
    sylbid
    3impia
    @4
    @2
    @16
    wcel
    #
    @24
    @2
    @22
    wceq
    #
    wi
    #
    vu
    @16
    wral
    #
    @28
    @0
    @1
    @45
    @3
    @1
    @0
    @34
    @45
    @35
    cA
    cN
    cV
    repsw
    sylan2
    3adant3
    @4
    @47
    vu
    @16
    @4
    @22
    @16
    wcel
    #
    wa
    #
    @23
    @46
    vn
    @14
    @50
    @9
    @14
    wcel
    #
    wa
    #
    @23
    @46
    @52
    @10
    @2
    @22
    @52
    @10
    @2
    @9
    ccsh
    co
    #
    @2
    @52
    cW
    @2
    @9
    ccsh
    @0
    @1
    @3
    @49
    @51
    simpll3
    oveq1d
    @52
    @0
    @34
    @9
    cz
    wcel
    #
    @53
    @2
    wceq
    @4
    @0
    @49
    @51
    @0
    @1
    @3
    simp1
    ad2antrr
    @4
    @34
    @49
    @51
    @1
    @0
    @34
    @3
    @35
    3ad2ant2
    ad2antrr
    @51
    @54
    @50
    @9
    cc0
    @13
    elfzoelz
    adantl
    cA
    @9
    cN
    cV
    repswcshw
    syl3anc
    eqtrd
    eqeq1d
    biimpd
    rexlimdva
    ralrimiva
    @27
    @48
    vw
    @2
    @16
    @11
    @2
    wceq
    #
    @26
    @47
    vu
    @16
    @55
    @25
    @46
    @24
    @11
    @2
    @22
    eqeq1
    imbi2d
    ralbidv
    rspcev
    syl2anc
    @15
    @24
    vw
    vu
    @16
    @25
    @12
    @23
    vn
    @14
    @11
    @22
    @10
    eqeq2
    rexbidv
    reu7
    sylanbrc
    @15
    vw
    vr
    @16
    reusn
    sylib
    @7
    @18
    vr
    cM
    @17
    @6
    cshwrepswhash1.m
    eqeq1i
    exbii
    sylibr
    @4
    cM
    cvv
    wcel
    #
    @5
    @8
    wb
    @0
    @1
    @3
    @56
    @29
    @3
    @33
    @56
    @36
    @30
    @31
    @56
    @32
    vw
    vn
    cM
    cV
    cW
    cshwrepswhash1.m
    cshwsex
    3ad2ant1
    syl6bi
    3impia
    cM
    cvv
    vr
    hash1snb
    syl
    mpbird
end
