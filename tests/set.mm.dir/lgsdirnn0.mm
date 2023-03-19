include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "clgs.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "simp2.mm"
include "cc.mm"
include "id.mm"
include "nn0z.mm"
include "lgscl.mm"
include "syl2anr.mm"
include "zcnd.mm"
include "adantr.mm"
include "mul01d.mm"
include "simpr.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"
include "wne.mm"
include "c1.mm"
include "cgcd.mm"
include "wb.mm"
include "0z.mm"
include "lgsne0.mm"
include "sylancr.mm"
include "gcdcom.mm"
include "nn0gcdid0.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "lgs1.mm"
include "adantl.mm"
include "oveq2.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "imp.mm"
include "oveq1d.mm"
include "ad2antrr.mm"
include "mulid2d.mm"
include "eqtr2d.mm"
include "pm2.61dane.mm"
include "ralrimiva.mm"
include "3ad2ant3.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "syl2anc.mm"
include "mulcomd.mm"
include "eqtr4d.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "mul02d.mm"
include "sylan9eqr.mm"
include "3eqtr4d.mm"
include "simp1.mm"
include "lgsdir.mm"
include "syl3anl3.mm"
include "pm2.61da2ne.mm"

theorem lgsdirnn0
  let cA: class A
  let cB: class B
  let cN: class N
  let vx: setvar x
  let cM: class M


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ N e. NN0 ) -> ( ( A x. B ) /L N ) = ( ( A /L N ) x. ( B /L N ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cA
    cB
    cmul
    co
    #
    cN
    clgs
    co
    #
    cA
    cN
    clgs
    co
    #
    cB
    cN
    clgs
    co
    #
    cmul
    co
    #
    wceq
    #
    cA
    cc0
    cB
    cc0
    @3
    cA
    cc0
    wceq
    #
    wa
    #
    cc0
    cN
    clgs
    co
    #
    @12
    @7
    cmul
    co
    #
    @5
    @8
    @11
    @12
    @7
    @12
    cmul
    co
    #
    @13
    @3
    @12
    @14
    wceq
    #
    @10
    @3
    @1
    @12
    vx
    cv
    #
    cN
    clgs
    co
    #
    @12
    cmul
    co
    #
    wceq
    #
    vx
    cz
    wral
    #
    @15
    @0
    @1
    @2
    simp2
    #
    @2
    @0
    @20
    @1
    @2
    @19
    vx
    cz
    @2
    @16
    cz
    wcel
    #
    wa
    #
    @19
    @12
    cc0
    @23
    @12
    cc0
    wceq
    #
    wa
    #
    @17
    cc0
    cmul
    co
    cc0
    @18
    @12
    @25
    @17
    @23
    @17
    cc
    wcel
    @24
    @23
    @17
    @22
    @22
    cN
    cz
    wcel
    #
    @17
    cz
    wcel
    @2
    @22
    id
    cN
    nn0z
    #
    @16
    cN
    lgscl
    syl2anr
    zcnd
    adantr
    mul01d
    @25
    @12
    cc0
    @17
    cmul
    @23
    @24
    simpr
    #
    oveq2d
    @28
    3eqtr4rd
    @23
    @12
    cc0
    wne
    #
    wa
    #
    @18
    c1
    @12
    cmul
    co
    @12
    @30
    @17
    c1
    @12
    cmul
    @23
    @29
    @17
    c1
    wceq
    #
    @23
    @29
    cc0
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @31
    @23
    cc0
    cz
    wcel
    #
    @26
    @29
    @33
    wb
    0z
    @2
    @26
    @22
    @27
    adantr
    #
    cc0
    cN
    lgsne0
    sylancr
    @23
    @33
    cN
    c1
    wceq
    #
    @31
    @23
    @32
    cN
    c1
    @23
    @32
    cN
    cc0
    cgcd
    co
    #
    cN
    @23
    @34
    @26
    @32
    @37
    wceq
    0z
    @35
    cc0
    cN
    gcdcom
    sylancr
    @2
    @37
    cN
    wceq
    @22
    cN
    nn0gcdid0
    adantr
    eqtrd
    eqeq1d
    @23
    @31
    @36
    @16
    c1
    clgs
    co
    #
    c1
    wceq
    #
    @22
    @39
    @2
    @16
    lgs1
    adantl
    @36
    @17
    @38
    c1
    cN
    c1
    @16
    clgs
    oveq2
    eqeq1d
    syl5ibrcom
    sylbid
    sylbid
    imp
    oveq1d
    @30
    @12
    @30
    @12
    @30
    @34
    @26
    @12
    cz
    wcel
    #
    0z
    @2
    @26
    @22
    @29
    @27
    ad2antrr
    cc0
    cN
    lgscl
    #
    sylancr
    zcnd
    mulid2d
    eqtr2d
    pm2.61dane
    ralrimiva
    3ad2ant3
    #
    @19
    @15
    vx
    cB
    cz
    @16
    cB
    wceq
    #
    @18
    @14
    @12
    @43
    @17
    @7
    @12
    cmul
    @16
    cB
    cN
    clgs
    oveq1
    oveq1d
    eqeq2d
    rspcv
    sylc
    adantr
    @11
    @12
    @7
    @3
    @12
    cc
    wcel
    @10
    @3
    @12
    @3
    @34
    @26
    @40
    0z
    @2
    @0
    @26
    @1
    @27
    3ad2ant3
    #
    @41
    sylancr
    zcnd
    adantr
    @3
    @7
    cc
    wcel
    @10
    @3
    @7
    @3
    @1
    @26
    @7
    cz
    wcel
    @21
    @44
    cB
    cN
    lgscl
    syl2anc
    zcnd
    adantr
    mulcomd
    eqtr4d
    @11
    @4
    cc0
    cN
    clgs
    @10
    @3
    @4
    cc0
    cB
    cmul
    co
    cc0
    cA
    cc0
    cB
    cmul
    oveq1
    @3
    cB
    @1
    @0
    cB
    cc
    wcel
    @2
    cB
    zcn
    3ad2ant2
    mul02d
    sylan9eqr
    oveq1d
    @11
    @6
    @12
    @7
    cmul
    @11
    cA
    cc0
    cN
    clgs
    @3
    @10
    simpr
    oveq1d
    oveq1d
    3eqtr4d
    @3
    cB
    cc0
    wceq
    #
    wa
    #
    @12
    @6
    @12
    cmul
    co
    #
    @5
    @8
    @3
    @12
    @47
    wceq
    #
    @45
    @3
    @0
    @20
    @48
    @0
    @1
    @2
    simp1
    #
    @42
    @19
    @48
    vx
    cA
    cz
    @16
    cA
    wceq
    #
    @18
    @47
    @12
    @50
    @17
    @6
    @12
    cmul
    @16
    cA
    cN
    clgs
    oveq1
    oveq1d
    eqeq2d
    rspcv
    sylc
    adantr
    @46
    @4
    cc0
    cN
    clgs
    @45
    @3
    @4
    cA
    cc0
    cmul
    co
    cc0
    cB
    cc0
    cA
    cmul
    oveq2
    @3
    cA
    @3
    cA
    @49
    zcnd
    mul01d
    sylan9eqr
    oveq1d
    @46
    @7
    @12
    @6
    cmul
    @46
    cB
    cc0
    cN
    clgs
    @3
    @45
    simpr
    oveq1d
    oveq2d
    3eqtr4d
    @2
    @0
    @1
    @26
    cA
    cc0
    wne
    cB
    cc0
    wne
    wa
    @9
    @27
    cA
    cB
    cN
    lgsdir
    syl3anl3
    pm2.61da2ne
end
