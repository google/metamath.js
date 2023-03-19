include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "clgs.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "simp3.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "sq1.mm"
include "eqeq2i.mm"
include "wb.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "1re.mm"
include "0le1.mm"
include "sq11.mm"
include "mpanr12.mm"
include "syl2anc.mm"
include "adantr.mm"
include "syl5bbr.mm"
include "biimpa.mm"
include "oveq1d.mm"
include "1lgs.mm"
include "ad2antlr.mm"
include "eqtrd.mm"
include "nn0z.mm"
include "ad2antrr.mm"
include "0z.mm"
include "lgscl.mm"
include "sylancl.mm"
include "zcnd.mm"
include "mulid2d.mm"
include "eqtr2d.mm"
include "wne.mm"
include "cc.mm"
include "sylan.mm"
include "mul01d.mm"
include "cif.mm"
include "lgs0.mm"
include "syl.mm"
include "ifnefalse.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "3eqtr4rd.mm"
include "pm2.61dane.mm"
include "ralrimiva.mm"
include "3ad2ant1.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcv.mm"
include "sylc.mm"
include "mulcomd.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "mul02d.mm"
include "sylan9eqr.mm"
include "simpr.mm"
include "3eqtr4d.mm"
include "simp2.mm"
include "lgsdi.mm"
include "syl3anl1.mm"
include "pm2.61da2ne.mm"

theorem lgsdinn0
  let cA: class A
  let cM: class M
  let cN: class N
  let vx: setvar x
  let cB: class B


  assert |- ( ( A e. NN0 /\ M e. ZZ /\ N e. ZZ ) -> ( A /L ( M x. N ) ) = ( ( A /L M ) x. ( A /L N ) ) )

  proof
    cA
    cn0
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cA
    cM
    cN
    cmul
    co
    #
    clgs
    co
    #
    cA
    cM
    clgs
    co
    #
    cA
    cN
    clgs
    co
    #
    cmul
    co
    #
    wceq
    #
    cM
    cc0
    cN
    cc0
    @3
    cM
    cc0
    wceq
    #
    wa
    #
    cA
    cc0
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
    @2
    @12
    cA
    vx
    cv
    #
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
    simp3
    #
    @0
    @1
    @20
    @2
    @0
    @19
    vx
    cz
    @0
    @16
    cz
    wcel
    #
    wa
    #
    @19
    cA
    c2
    cexp
    co
    #
    c1
    @23
    @24
    c1
    wceq
    #
    wa
    #
    @18
    c1
    @12
    cmul
    co
    @12
    @26
    @17
    c1
    @12
    cmul
    @26
    @17
    c1
    @16
    clgs
    co
    #
    c1
    @26
    cA
    c1
    @16
    clgs
    @23
    @25
    cA
    c1
    wceq
    #
    @25
    @24
    c1
    c2
    cexp
    co
    #
    wceq
    #
    @23
    @28
    @29
    c1
    @24
    sq1
    eqeq2i
    @0
    @30
    @28
    wb
    #
    @22
    @0
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    @31
    cA
    nn0re
    cA
    nn0ge0
    @32
    @33
    wa
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @31
    1re
    0le1
    cA
    c1
    sq11
    mpanr12
    syl2anc
    adantr
    syl5bbr
    biimpa
    oveq1d
    @22
    @27
    c1
    wceq
    @0
    @25
    @16
    1lgs
    ad2antlr
    eqtrd
    oveq1d
    @26
    @12
    @26
    @12
    @26
    cA
    cz
    wcel
    #
    cc0
    cz
    wcel
    #
    @12
    cz
    wcel
    #
    @0
    @34
    @22
    @25
    cA
    nn0z
    #
    ad2antrr
    0z
    cA
    cc0
    lgscl
    #
    sylancl
    zcnd
    mulid2d
    eqtr2d
    @23
    @24
    c1
    wne
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
    @40
    @17
    @23
    @17
    cc
    wcel
    @39
    @23
    @17
    @0
    @34
    @22
    @17
    cz
    wcel
    @37
    cA
    @16
    lgscl
    sylan
    zcnd
    adantr
    mul01d
    @40
    @12
    cc0
    @17
    cmul
    @23
    @39
    @12
    @25
    c1
    cc0
    cif
    #
    cc0
    @23
    @34
    @12
    @41
    wceq
    @0
    @34
    @22
    @37
    adantr
    cA
    lgs0
    syl
    @24
    c1
    c1
    cc0
    ifnefalse
    sylan9eq
    #
    oveq2d
    @42
    3eqtr4rd
    pm2.61dane
    ralrimiva
    3ad2ant1
    #
    @19
    @15
    vx
    cN
    cz
    @16
    cN
    wceq
    #
    @18
    @14
    @12
    @44
    @17
    @7
    @12
    cmul
    @16
    cN
    cA
    clgs
    oveq2
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
    @35
    @36
    @0
    @1
    @34
    @2
    @37
    3ad2ant1
    #
    0z
    @38
    sylancl
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
    @34
    @2
    @7
    cz
    wcel
    @45
    @21
    cA
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
    cA
    clgs
    @10
    @3
    @4
    cc0
    cN
    cmul
    co
    cc0
    cM
    cc0
    cN
    cmul
    oveq1
    @3
    cN
    @3
    cN
    @21
    zcnd
    mul02d
    sylan9eqr
    oveq2d
    @11
    @6
    @12
    @7
    cmul
    @11
    cM
    cc0
    cA
    clgs
    @3
    @10
    simpr
    oveq2d
    oveq1d
    3eqtr4d
    @3
    cN
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
    @48
    wceq
    #
    @46
    @3
    @1
    @20
    @49
    @0
    @1
    @2
    simp2
    #
    @43
    @19
    @49
    vx
    cM
    cz
    @16
    cM
    wceq
    #
    @18
    @48
    @12
    @51
    @17
    @6
    @12
    cmul
    @16
    cM
    cA
    clgs
    oveq2
    oveq1d
    eqeq2d
    rspcv
    sylc
    adantr
    @47
    @4
    cc0
    cA
    clgs
    @46
    @3
    @4
    cM
    cc0
    cmul
    co
    cc0
    cN
    cc0
    cM
    cmul
    oveq2
    @3
    cM
    @3
    cM
    @50
    zcnd
    mul01d
    sylan9eqr
    oveq2d
    @47
    @7
    @12
    @6
    cmul
    @47
    cN
    cc0
    cA
    clgs
    @3
    @46
    simpr
    oveq2d
    oveq2d
    3eqtr4d
    @0
    @34
    @1
    @2
    cM
    cc0
    wne
    cN
    cc0
    wne
    wa
    @9
    @37
    cA
    cM
    cN
    lgsdi
    syl3anl1
    pm2.61da2ne
end
