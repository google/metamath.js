include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "crmx.mm"
include "crmy.mm"
include "cneg.mm"
include "wo.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "2z.mm"
include "simplr.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "zsubcl.mm"
include "adantl.mm"
include "divides.mm"
include "syl2anc.mm"
include "caddc.mm"
include "simplll.mm"
include "simplrr.mm"
include "simpllr.mm"
include "simpr.mm"
include "jm2.25.mm"
include "syl121anc.mm"
include "adantr.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cc.mm"
include "zcn.mm"
include "pncan3.mm"
include "syl2anr.mm"
include "ad2antlr.mm"
include "sylan9eqr.mm"
include "eqidd.mm"
include "acongeq12d.mm"
include "mpbid.mm"
include "ex.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "simprl.mm"
include "znegcl.mm"
include "ad2antll.mm"
include "zsubcld.mm"
include "w3a.mm"
include "cn0.mm"
include "frmx.mm"
include "fovcl.mm"
include "nn0zd.mm"
include "simplrl.mm"
include "frmy.mm"
include "3jca.mm"
include "negcld.mm"
include "rmyneg.mm"
include "acongneg2.mm"
include "jaod.mm"

theorem jm2.26a
  let cA: class A
  let cK: class K
  let cM: class M
  let cN: class N
  let va: setvar a


  assert |- ( ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) /\ ( K e. ZZ /\ M e. ZZ ) ) -> ( ( ( 2 x. N ) || ( K - M ) \/ ( 2 x. N ) || ( K - -u M ) ) -> ( ( A rmX N ) || ( ( A rmY K ) - ( A rmY M ) ) \/ ( A rmX N ) || ( ( A rmY K ) - -u ( A rmY M ) ) ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    #
    wa
    #
    c2
    cN
    cmul
    co
    #
    cK
    cM
    cmin
    co
    #
    cdvds
    wbr
    #
    cA
    cN
    crmx
    co
    #
    cA
    cK
    crmy
    co
    #
    cA
    cM
    crmy
    co
    #
    cmin
    co
    cdvds
    wbr
    @11
    @12
    @13
    cneg
    #
    cmin
    co
    cdvds
    wbr
    #
    wo
    #
    @8
    cK
    cM
    cneg
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    @7
    @10
    va
    cv
    #
    @8
    cmul
    co
    #
    @9
    wceq
    #
    va
    cz
    wrex
    #
    @16
    @7
    @8
    cz
    wcel
    #
    @9
    cz
    wcel
    #
    @10
    @23
    wb
    @7
    c2
    cz
    wcel
    @2
    @24
    2z
    @1
    @2
    @6
    simplr
    c2
    cN
    zmulcl
    sylancr
    #
    @6
    @25
    @3
    cK
    cM
    zsubcl
    adantl
    va
    @8
    @9
    divides
    syl2anc
    @7
    @22
    @16
    va
    cz
    @7
    @20
    cz
    wcel
    #
    wa
    #
    @22
    @16
    @28
    @22
    wa
    #
    @11
    cA
    cM
    @21
    caddc
    co
    #
    crmy
    co
    #
    @13
    cmin
    co
    cdvds
    wbr
    @11
    @31
    @14
    cmin
    co
    cdvds
    wbr
    wo
    #
    @16
    @28
    @32
    @22
    @28
    @1
    @5
    @2
    @27
    @32
    @1
    @2
    @6
    @27
    simplll
    #
    @3
    @4
    @5
    @27
    simplrr
    #
    @1
    @2
    @6
    @27
    simpllr
    #
    @7
    @27
    simpr
    #
    cA
    @20
    cM
    cN
    jm2.25
    syl121anc
    adantr
    @29
    @11
    @31
    @12
    @13
    @13
    @22
    @28
    @31
    cA
    cM
    @9
    caddc
    co
    #
    crmy
    co
    @12
    @22
    @30
    @37
    cA
    crmy
    @21
    @9
    cM
    caddc
    oveq2
    oveq2d
    @28
    @37
    cK
    cA
    crmy
    @6
    @37
    cK
    wceq
    #
    @3
    @27
    @5
    cM
    cc
    wcel
    cK
    cc
    wcel
    #
    @38
    @4
    cM
    zcn
    #
    cK
    zcn
    #
    cM
    cK
    pncan3
    syl2anr
    ad2antlr
    oveq2d
    sylan9eqr
    @29
    @13
    eqidd
    acongeq12d
    mpbid
    ex
    rexlimdva
    sylbid
    @7
    @19
    @21
    @18
    wceq
    #
    va
    cz
    wrex
    #
    @16
    @7
    @24
    @18
    cz
    wcel
    @19
    @43
    wb
    @26
    @7
    cK
    @17
    @3
    @4
    @5
    simprl
    @5
    @17
    cz
    wcel
    #
    @3
    @4
    cM
    znegcl
    ad2antll
    #
    zsubcld
    va
    @8
    @18
    divides
    syl2anc
    @7
    @42
    @16
    va
    cz
    @28
    @42
    @16
    @28
    @42
    wa
    #
    @11
    cz
    wcel
    #
    @12
    cz
    wcel
    #
    @13
    cz
    wcel
    #
    w3a
    #
    @15
    @11
    @12
    @14
    cneg
    cmin
    co
    cdvds
    wbr
    wo
    #
    @16
    @28
    @50
    @42
    @28
    @47
    @48
    @49
    @28
    @1
    @2
    @47
    @33
    @35
    @3
    @11
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    nn0zd
    syl2anc
    @28
    @1
    @4
    @48
    @33
    @3
    @4
    @5
    @27
    simplrl
    cA
    cK
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    @28
    @1
    @5
    @49
    @33
    @34
    cA
    cM
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    syl2anc
    3jca
    adantr
    @46
    @11
    cA
    @17
    @21
    caddc
    co
    #
    crmy
    co
    #
    cA
    @17
    crmy
    co
    #
    cmin
    co
    cdvds
    wbr
    @11
    @53
    @54
    cneg
    cmin
    co
    cdvds
    wbr
    wo
    #
    @51
    @28
    @55
    @42
    @28
    @1
    @44
    @2
    @27
    @55
    @33
    @7
    @44
    @27
    @45
    adantr
    @35
    @36
    cA
    @20
    @17
    cN
    jm2.25
    syl121anc
    adantr
    @46
    @11
    @53
    @12
    @54
    @14
    @42
    @28
    @53
    cA
    @17
    @18
    caddc
    co
    #
    crmy
    co
    @12
    @42
    @52
    @56
    cA
    crmy
    @21
    @18
    @17
    caddc
    oveq2
    oveq2d
    @28
    @56
    cK
    cA
    crmy
    @6
    @56
    cK
    wceq
    #
    @3
    @27
    @5
    @17
    cc
    wcel
    @39
    @57
    @4
    @5
    cM
    @40
    negcld
    @41
    @17
    cK
    pncan3
    syl2anr
    ad2antlr
    oveq2d
    sylan9eqr
    @28
    @54
    @14
    wceq
    #
    @42
    @28
    @1
    @5
    @58
    @33
    @34
    cA
    cM
    rmyneg
    syl2anc
    adantr
    acongeq12d
    mpbid
    @11
    @12
    @13
    acongneg2
    syl2anc
    ex
    rexlimdva
    sylbid
    jaod
end
