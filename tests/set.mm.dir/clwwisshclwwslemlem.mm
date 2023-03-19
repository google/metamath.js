include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cc0.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "cmo.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "1cnd.mm"
include "3ad2ant3.mm"
include "add32d.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "3ad2ant1.mm"
include "preq2d.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "cn0.mm"
include "cn.mm"
include "zaddcl.mm"
include "3adant1.mm"
include "eluz2nn.mm"
include "zmodcld.mm"
include "adantr.mm"
include "uz2m1nn.mm"
include "simpr.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "fveq2.mm"
include "oveq1.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "syl.mm"
include "cr.mm"
include "crp.mm"
include "zred.mm"
include "nnrpd.mm"
include "modltm1p1mod.mm"
include "syl3anc.mm"
include "sylibrd.mm"
include "impancom.mm"
include "3adant3.mm"
include "wn.mm"
include "zmodfzo.mm"
include "syl2anc.mm"
include "elfzonlteqm1.mm"
include "eqcomd.mm"
include "ex.mm"
include "adantl.mm"
include "zre.mm"
include "readdcl.mm"
include "syl2an.mm"
include "jca.mm"
include "modm1p1mod0.mm"
include "sylc.mm"
include "biimpd.mm"
include "syld.mm"
include "com23.mm"
include "imp.mm"
include "3adant2.mm"
include "pm2.61d.mm"
include "eqeltrd.mm"

theorem clwwisshclwwslemlem
  let cA: class A
  let cB: class B
  let cR: class R
  let vi: setvar i
  let cL: class L
  let cW: class W

  disjoint A i
  disjoint B i
  disjoint L i
  disjoint R i
  disjoint W i
  assert |- ( ( ( L e. ( ZZ>= ` 2 ) /\ A e. ZZ /\ B e. ZZ ) /\ A. i e. ( 0 ..^ ( L - 1 ) ) { ( W ` i ) , ( W ` ( i + 1 ) ) } e. R /\ { ( W ` ( L - 1 ) ) , ( W ` 0 ) } e. R ) -> { ( W ` ( ( A + B ) mod L ) ) , ( W ` ( ( ( A + 1 ) + B ) mod L ) ) } e. R )

  proof
    cL
    c2
    cuz
    cfv
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    w3a
    #
    vi
    cv
    #
    cW
    cfv
    #
    @4
    c1
    caddc
    co
    #
    cW
    cfv
    #
    cpr
    #
    cR
    wcel
    #
    vi
    cc0
    cL
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @10
    cW
    cfv
    #
    cc0
    cW
    cfv
    #
    cpr
    #
    cR
    wcel
    #
    w3a
    #
    cA
    cB
    caddc
    co
    #
    cL
    cmo
    co
    #
    cW
    cfv
    #
    cA
    c1
    caddc
    co
    cB
    caddc
    co
    #
    cL
    cmo
    co
    #
    cW
    cfv
    #
    cpr
    @20
    @18
    c1
    caddc
    co
    #
    cL
    cmo
    co
    #
    cW
    cfv
    #
    cpr
    #
    cR
    @17
    @23
    @26
    @20
    @3
    @12
    @23
    @26
    wceq
    @16
    @3
    @22
    @25
    cW
    @3
    @21
    @24
    cL
    cmo
    @3
    cA
    c1
    cB
    @1
    @0
    cA
    cc
    wcel
    @2
    cA
    zcn
    3ad2ant2
    @3
    1cnd
    @2
    @0
    cB
    cc
    wcel
    @1
    cB
    zcn
    3ad2ant3
    add32d
    oveq1d
    fveq2d
    3ad2ant1
    preq2d
    @17
    @19
    @10
    clt
    wbr
    #
    @27
    cR
    wcel
    #
    @3
    @12
    @28
    @29
    wi
    @16
    @3
    @28
    @12
    @29
    @3
    @28
    wa
    #
    @12
    @20
    @19
    c1
    caddc
    co
    #
    cW
    cfv
    #
    cpr
    #
    cR
    wcel
    #
    @29
    @30
    @19
    @11
    wcel
    #
    @12
    @34
    wi
    @30
    @19
    cn0
    wcel
    #
    @10
    cn
    wcel
    #
    @28
    @35
    @3
    @36
    @28
    @3
    @18
    cL
    @1
    @2
    @18
    cz
    wcel
    #
    @0
    cA
    cB
    zaddcl
    #
    3adant1
    #
    @0
    @1
    cL
    cn
    wcel
    #
    @2
    cL
    eluz2nn
    #
    3ad2ant1
    #
    zmodcld
    adantr
    @3
    @37
    @28
    @0
    @1
    @37
    @2
    cL
    uz2m1nn
    3ad2ant1
    adantr
    @3
    @28
    simpr
    #
    @19
    @10
    elfzo0
    syl3anbrc
    @9
    @34
    vi
    @19
    @11
    @4
    @19
    wceq
    #
    @8
    @33
    cR
    @45
    @5
    @20
    @7
    @32
    @4
    @19
    cW
    fveq2
    @45
    @6
    @31
    cW
    @4
    @19
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    rspcv
    syl
    @30
    @27
    @33
    cR
    @30
    @26
    @32
    @20
    @30
    @25
    @31
    cW
    @30
    @18
    cr
    wcel
    #
    cL
    crp
    wcel
    #
    @28
    @25
    @31
    wceq
    @3
    @46
    @28
    @1
    @2
    @46
    @0
    @1
    @2
    wa
    @18
    @39
    zred
    3adant1
    adantr
    @3
    @47
    @28
    @0
    @1
    @47
    @2
    @0
    cL
    @42
    nnrpd
    3ad2ant1
    #
    adantr
    @44
    @18
    cL
    modltm1p1mod
    syl3anc
    fveq2d
    preq2d
    eleq1d
    sylibrd
    impancom
    3adant3
    @3
    @16
    @28
    wn
    #
    @29
    wi
    #
    @12
    @3
    @16
    @50
    @3
    @49
    @16
    @29
    @3
    @49
    @10
    @19
    wceq
    #
    @16
    @29
    wi
    #
    @3
    @19
    cc0
    cL
    cfzo
    co
    wcel
    #
    @49
    @51
    wi
    @3
    @38
    @41
    @53
    @40
    @43
    @18
    cL
    zmodfzo
    syl2anc
    @53
    @49
    @51
    @53
    @49
    wa
    @19
    @10
    @19
    cL
    elfzonlteqm1
    eqcomd
    ex
    syl
    @3
    @51
    @52
    @3
    @51
    wa
    #
    @16
    @29
    @54
    @15
    @27
    cR
    @54
    @13
    @20
    @14
    @26
    @51
    @13
    @20
    wceq
    @3
    @10
    @19
    cW
    fveq2
    adantl
    @54
    cc0
    @25
    cW
    @54
    @25
    cc0
    @54
    @46
    @47
    wa
    #
    @19
    @10
    wceq
    @25
    cc0
    wceq
    @3
    @55
    @51
    @3
    @46
    @47
    @1
    @2
    @46
    @0
    @1
    cA
    cr
    wcel
    cB
    cr
    wcel
    @46
    @2
    cA
    zre
    cB
    zre
    cA
    cB
    readdcl
    syl2an
    3adant1
    @48
    jca
    adantr
    @54
    @10
    @19
    @3
    @51
    simpr
    eqcomd
    @18
    cL
    modm1p1mod0
    sylc
    eqcomd
    fveq2d
    preq12d
    eleq1d
    biimpd
    ex
    syld
    com23
    imp
    3adant2
    pm2.61d
    eqeltrd
end
