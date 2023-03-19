include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cxad.mm"
include "co.mm"
include "cxne.mm"
include "cneg.mm"
include "wceq.mm"
include "rexneg.mm"
include "adantl.mm"
include "oveq2d.mm"
include "cmnf.mm"
include "renegcl.mm"
include "ad2antlr.mm"
include "cpnf.mm"
include "wne.mm"
include "rexr.mm"
include "renepnf.mm"
include "xaddmnf2.mm"
include "syl2anc.mm"
include "syl.mm"
include "oveq1.mm"
include "sylan9eqr.mm"
include "oveq1d.mm"
include "simpr.mm"
include "3eqtr4d.mm"
include "simpll.mm"
include "renemnf.mm"
include "xaddass.mm"
include "syl222anc.mm"
include "cc0.mm"
include "caddc.mm"
include "simplr.mm"
include "rexadd.mm"
include "recnd.mm"
include "negidd.mm"
include "eqtrd.mm"
include "xaddid1.mm"
include "ad2antrr.mm"
include "pm2.61dane.mm"

theorem xpncan
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR ) -> ( ( A +e B ) +e -e B ) = A )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cxad
    co
    #
    cB
    cxne
    #
    cxad
    co
    @3
    cB
    cneg
    #
    cxad
    co
    #
    cA
    @2
    @4
    @5
    @3
    cxad
    @1
    @4
    @5
    wceq
    @0
    cB
    rexneg
    adantl
    oveq2d
    @2
    @6
    cA
    wceq
    cA
    cmnf
    @2
    cA
    cmnf
    wceq
    #
    wa
    #
    cmnf
    @5
    cxad
    co
    #
    cmnf
    @6
    cA
    @8
    @5
    cr
    wcel
    #
    @9
    cmnf
    wceq
    #
    @1
    @10
    @0
    @7
    cB
    renegcl
    #
    ad2antlr
    @10
    @5
    cxr
    wcel
    #
    @5
    cpnf
    wne
    @11
    @5
    rexr
    #
    @5
    renepnf
    @5
    xaddmnf2
    syl2anc
    syl
    @8
    @3
    cmnf
    @5
    cxad
    @7
    @2
    @3
    cmnf
    cB
    cxad
    co
    #
    cmnf
    cA
    cmnf
    cB
    cxad
    oveq1
    @1
    @15
    cmnf
    wceq
    #
    @0
    @1
    cB
    cxr
    wcel
    #
    cB
    cpnf
    wne
    @16
    cB
    rexr
    #
    cB
    renepnf
    cB
    xaddmnf2
    syl2anc
    adantl
    sylan9eqr
    oveq1d
    @2
    @7
    simpr
    3eqtr4d
    @2
    cA
    cmnf
    wne
    #
    wa
    #
    @6
    cA
    cB
    @5
    cxad
    co
    #
    cxad
    co
    #
    cA
    @20
    @0
    @19
    @17
    cB
    cmnf
    wne
    #
    @13
    @5
    cmnf
    wne
    #
    @6
    @22
    wceq
    @0
    @1
    @19
    simpll
    @2
    @19
    simpr
    @1
    @17
    @0
    @19
    @18
    ad2antlr
    @1
    @23
    @0
    @19
    cB
    renemnf
    ad2antlr
    @20
    @10
    @13
    @1
    @10
    @0
    @19
    @12
    ad2antlr
    #
    @14
    syl
    @20
    @10
    @24
    @25
    @5
    renemnf
    syl
    cA
    cB
    @5
    xaddass
    syl222anc
    @20
    @22
    cA
    cc0
    cxad
    co
    #
    cA
    @20
    @21
    cc0
    cA
    cxad
    @20
    @21
    cB
    @5
    caddc
    co
    #
    cc0
    @20
    @1
    @10
    @21
    @27
    wceq
    @0
    @1
    @19
    simplr
    #
    @25
    cB
    @5
    rexadd
    syl2anc
    @20
    cB
    @20
    cB
    @28
    recnd
    negidd
    eqtrd
    oveq2d
    @0
    @26
    cA
    wceq
    @1
    @19
    cA
    xaddid1
    ad2antrr
    eqtrd
    eqtrd
    pm2.61dane
    eqtrd
end
