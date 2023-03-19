include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "wrex.mm"
include "c1.mm"
include "simpl.mm"
include "anim2i.mm"
include "zeqzmulgcd.mm"
include "syl.mm"
include "3adant3.mm"
include "adantlr.mm"
include "ancoms.mm"
include "reeanv.mm"
include "cc.mm"
include "zcn.mm"
include "adantl.mm"
include "cn0.mm"
include "gcdcl.mm"
include "nn0cnd.mm"
include "adantr.mm"
include "mulcomd.mm"
include "simp3.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "ad2antrr.mm"
include "wb.mm"
include "eqeq1.mm"
include "mpbird.mm"
include "simpr.mm"
include "ancomd.mm"
include "gcdcom.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "sylan9eqr.mm"
include "cdiv.mm"
include "3ad2ant1.mm"
include "simp1.mm"
include "3ad2ant2.mm"
include "gcdcld.mm"
include "gcdeq0.mm"
include "syl6bi.mm"
include "necon3d.mm"
include "impr.mm"
include "divmul3d.mm"
include "bicomd.mm"
include "eqeq2d.mm"
include "bitr2d.mm"
include "anbi12d.mm"
include "wi.mm"
include "3anass.mm"
include "biimpri.mm"
include "divgcdcoprm0.mm"
include "oveq12.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "imp.mm"
include "3jca.mm"
include "ex.mm"
include "reximdva.mm"
include "syl5bir.mm"
include "mp2and.mm"

theorem divgcdcoprmex
  let cA: class A
  let cB: class B
  let cM: class M
  let va: setvar a
  let vb: setvar b

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint B b
  disjoint M a
  disjoint M b
  assert |- ( ( A e. ZZ /\ ( B e. ZZ /\ B =/= 0 ) /\ M = ( A gcd B ) ) -> E. a e. ZZ E. b e. ZZ ( A = ( M x. a ) /\ B = ( M x. b ) /\ ( a gcd b ) = 1 ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    cM
    cA
    cB
    cgcd
    co
    #
    wceq
    #
    w3a
    #
    cA
    va
    cv
    #
    @4
    cmul
    co
    #
    wceq
    #
    va
    cz
    wrex
    #
    cB
    vb
    cv
    #
    cB
    cA
    cgcd
    co
    #
    cmul
    co
    #
    wceq
    #
    vb
    cz
    wrex
    #
    cA
    cM
    @7
    cmul
    co
    #
    wceq
    #
    cB
    cM
    @11
    cmul
    co
    #
    wceq
    #
    @7
    @11
    cgcd
    co
    #
    c1
    wceq
    #
    w3a
    #
    vb
    cz
    wrex
    #
    va
    cz
    wrex
    #
    @0
    @3
    @10
    @5
    @0
    @3
    wa
    #
    @0
    @1
    wa
    #
    @10
    @3
    @1
    @0
    @1
    @2
    simpl
    #
    anim2i
    #
    cA
    cB
    va
    zeqzmulgcd
    syl
    3adant3
    @0
    @3
    @15
    @5
    @3
    @0
    @15
    @1
    @0
    @15
    @2
    cB
    cA
    vb
    zeqzmulgcd
    adantlr
    ancoms
    3adant3
    @10
    @15
    wa
    @9
    @14
    wa
    #
    vb
    cz
    wrex
    #
    va
    cz
    wrex
    @6
    @24
    @9
    @14
    va
    vb
    cz
    cz
    reeanv
    @6
    @30
    @23
    va
    cz
    @6
    @7
    cz
    wcel
    #
    wa
    #
    @29
    @22
    vb
    cz
    @32
    @11
    cz
    wcel
    #
    wa
    #
    @29
    @22
    @34
    @29
    wa
    #
    @17
    @19
    @21
    @35
    @17
    @8
    @16
    wceq
    #
    @32
    @36
    @33
    @29
    @32
    @8
    @4
    @7
    cmul
    co
    #
    @16
    @32
    @7
    @4
    @31
    @7
    cc
    wcel
    #
    @6
    @7
    zcn
    adantl
    #
    @6
    @4
    cc
    wcel
    #
    @31
    @0
    @3
    @40
    @5
    @25
    @4
    @25
    @26
    @4
    cn0
    wcel
    #
    @28
    cA
    cB
    gcdcl
    syl
    #
    nn0cnd
    3adant3
    adantr
    mulcomd
    @6
    @37
    @16
    wceq
    @31
    @6
    @4
    cM
    @7
    cmul
    @6
    cM
    @4
    @0
    @3
    @5
    simp3
    eqcomd
    #
    oveq1d
    adantr
    eqtrd
    ad2antrr
    @29
    @17
    @36
    wb
    #
    @34
    @9
    @44
    @14
    cA
    @8
    @16
    eqeq1
    adantr
    adantl
    mpbird
    @29
    @34
    cB
    @13
    @18
    @9
    @14
    simpr
    @6
    @33
    @13
    @18
    wceq
    @31
    @6
    @33
    wa
    #
    @13
    @11
    @4
    cmul
    co
    #
    @4
    @11
    cmul
    co
    @18
    @6
    @13
    @46
    wceq
    @33
    @6
    @12
    @4
    @11
    cmul
    @0
    @3
    @12
    @4
    wceq
    #
    @5
    @25
    @1
    @0
    wa
    @47
    @25
    @0
    @1
    @28
    ancomd
    cB
    cA
    gcdcom
    syl
    3adant3
    oveq2d
    adantr
    @45
    @11
    @4
    @33
    @11
    cc
    wcel
    #
    @6
    @11
    zcn
    #
    adantl
    @45
    @4
    @6
    @41
    @33
    @0
    @3
    @41
    @5
    @42
    3adant3
    adantr
    nn0cnd
    mulcomd
    @45
    @4
    cM
    @11
    cmul
    @6
    @4
    cM
    wceq
    @33
    @43
    adantr
    oveq1d
    3eqtrd
    adantlr
    sylan9eqr
    @34
    @29
    @21
    @34
    @29
    cA
    @4
    cdiv
    co
    #
    @7
    wceq
    #
    cB
    @4
    cdiv
    co
    #
    @11
    wceq
    #
    wa
    #
    @21
    @34
    @9
    @51
    @14
    @53
    @34
    @51
    @9
    @34
    cA
    @7
    @4
    @6
    cA
    cc
    wcel
    #
    @31
    @33
    @0
    @3
    @55
    @5
    cA
    zcn
    3ad2ant1
    ad2antrr
    @32
    @38
    @33
    @39
    adantr
    @6
    @40
    @31
    @33
    @6
    @4
    @6
    cA
    cB
    @0
    @3
    @5
    simp1
    @3
    @0
    @1
    @5
    @27
    3ad2ant2
    gcdcld
    nn0cnd
    ad2antrr
    #
    @6
    @4
    cc0
    wne
    #
    @31
    @33
    @0
    @3
    @57
    @5
    @0
    @1
    @2
    @57
    @26
    @4
    cc0
    cB
    cc0
    @26
    @4
    cc0
    wceq
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wa
    @59
    cA
    cB
    gcdeq0
    @58
    @59
    simpr
    syl6bi
    necon3d
    impr
    3adant3
    ad2antrr
    #
    divmul3d
    bicomd
    @34
    @53
    cB
    @46
    wceq
    @14
    @34
    cB
    @11
    @4
    @6
    cB
    cc
    wcel
    #
    @31
    @33
    @3
    @0
    @61
    @5
    @1
    @61
    @2
    cB
    zcn
    adantr
    3ad2ant2
    ad2antrr
    @33
    @48
    @32
    @49
    adantl
    @56
    @60
    divmul3d
    @34
    @46
    @13
    cB
    @34
    @4
    @12
    @11
    cmul
    @6
    @4
    @12
    wceq
    #
    @31
    @33
    @6
    @26
    @62
    @0
    @3
    @26
    @5
    @28
    3adant3
    cA
    cB
    gcdcom
    syl
    ad2antrr
    oveq2d
    eqeq2d
    bitr2d
    anbi12d
    @6
    @54
    @21
    wi
    @31
    @33
    @6
    @50
    @52
    cgcd
    co
    #
    c1
    wceq
    #
    @54
    @21
    @6
    @0
    @1
    @2
    w3a
    #
    @64
    @0
    @3
    @65
    @5
    @65
    @25
    @0
    @1
    @2
    3anass
    biimpri
    3adant3
    cA
    cB
    divgcdcoprm0
    syl
    @54
    @63
    @20
    c1
    @50
    @7
    @52
    @11
    cgcd
    oveq12
    eqeq1d
    syl5ibcom
    ad2antrr
    sylbid
    imp
    3jca
    ex
    reximdva
    reximdva
    syl5bir
    mp2and
end
