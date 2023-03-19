include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "cxad.mm"
include "co.mm"
include "elxr.mm"
include "wa.mm"
include "caddc.mm"
include "cc.mm"
include "recn.mm"
include "addcom.mm"
include "syl2an.mm"
include "rexadd.mm"
include "ancoms.mm"
include "3eqtr4d.mm"
include "oveq2.mm"
include "wne.mm"
include "rexr.mm"
include "renemnf.mm"
include "xaddpnf1.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "oveq1.mm"
include "xaddpnf2.mm"
include "eqtr4d.mm"
include "renepnf.mm"
include "xaddmnf1.mm"
include "xaddmnf2.mm"
include "3jaodan.mm"
include "sylan2b.mm"
include "cc0.mm"
include "pnfaddmnf.mm"
include "mnfaddpnf.mm"
include "eqtr4i.mm"
include "simpr.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "3eqtr4a.mm"
include "pm2.61dane.mm"
include "adantl.mm"
include "simpl.mm"
include "3jaoian.mm"
include "sylanb.mm"

theorem xaddcom
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A +e B ) = ( B +e A ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    w3o
    cB
    cxr
    wcel
    #
    cA
    cB
    cxad
    co
    #
    cB
    cA
    cxad
    co
    #
    wceq
    #
    cA
    elxr
    @1
    @4
    @7
    @2
    @3
    @4
    @1
    cB
    cr
    wcel
    #
    cB
    cpnf
    wceq
    #
    cB
    cmnf
    wceq
    #
    w3o
    @7
    cB
    elxr
    @1
    @8
    @7
    @9
    @10
    @1
    @8
    wa
    cA
    cB
    caddc
    co
    #
    cB
    cA
    caddc
    co
    #
    @5
    @6
    @1
    cA
    cc
    wcel
    cB
    cc
    wcel
    @11
    @12
    wceq
    @8
    cA
    recn
    cB
    recn
    cA
    cB
    addcom
    syl2an
    cA
    cB
    rexadd
    @8
    @1
    @6
    @12
    wceq
    cB
    cA
    rexadd
    ancoms
    3eqtr4d
    @1
    @9
    wa
    @5
    cpnf
    @6
    @9
    @1
    @5
    cA
    cpnf
    cxad
    co
    #
    cpnf
    cB
    cpnf
    cA
    cxad
    oveq2
    @1
    @0
    cA
    cmnf
    wne
    #
    @13
    cpnf
    wceq
    cA
    rexr
    #
    cA
    renemnf
    #
    cA
    xaddpnf1
    syl2anc
    sylan9eqr
    @9
    @1
    @6
    cpnf
    cA
    cxad
    co
    #
    cpnf
    cB
    cpnf
    cA
    cxad
    oveq1
    @1
    @0
    @14
    @17
    cpnf
    wceq
    @15
    @16
    cA
    xaddpnf2
    syl2anc
    sylan9eqr
    eqtr4d
    @1
    @10
    wa
    @5
    cmnf
    @6
    @10
    @1
    @5
    cA
    cmnf
    cxad
    co
    #
    cmnf
    cB
    cmnf
    cA
    cxad
    oveq2
    @1
    @0
    cA
    cpnf
    wne
    #
    @18
    cmnf
    wceq
    @15
    cA
    renepnf
    #
    cA
    xaddmnf1
    syl2anc
    sylan9eqr
    @10
    @1
    @6
    cmnf
    cA
    cxad
    co
    #
    cmnf
    cB
    cmnf
    cA
    cxad
    oveq1
    @1
    @0
    @19
    @21
    cmnf
    wceq
    @15
    @20
    cA
    xaddmnf2
    syl2anc
    sylan9eqr
    eqtr4d
    3jaodan
    sylan2b
    @2
    @4
    wa
    #
    cpnf
    cB
    cxad
    co
    #
    cB
    cpnf
    cxad
    co
    #
    @5
    @6
    @4
    @23
    @24
    wceq
    #
    @2
    @4
    @25
    cB
    cmnf
    @4
    @10
    wa
    #
    cpnf
    cmnf
    cxad
    co
    #
    cmnf
    cpnf
    cxad
    co
    #
    @23
    @24
    @27
    cc0
    @28
    pnfaddmnf
    mnfaddpnf
    eqtr4i
    @26
    cB
    cmnf
    cpnf
    cxad
    @4
    @10
    simpr
    #
    oveq2d
    @26
    cB
    cmnf
    cpnf
    cxad
    @29
    oveq1d
    3eqtr4a
    @4
    cB
    cmnf
    wne
    wa
    @23
    cpnf
    @24
    cB
    xaddpnf2
    cB
    xaddpnf1
    eqtr4d
    pm2.61dane
    adantl
    @22
    cA
    cpnf
    cB
    cxad
    @2
    @4
    simpl
    #
    oveq1d
    @22
    cA
    cpnf
    cB
    cxad
    @30
    oveq2d
    3eqtr4d
    @3
    @4
    wa
    #
    cmnf
    cB
    cxad
    co
    #
    cB
    cmnf
    cxad
    co
    #
    @5
    @6
    @4
    @32
    @33
    wceq
    #
    @3
    @4
    @34
    cB
    cpnf
    @4
    @9
    wa
    #
    @28
    @27
    @32
    @33
    @28
    cc0
    @27
    mnfaddpnf
    pnfaddmnf
    eqtr4i
    @35
    cB
    cpnf
    cmnf
    cxad
    @4
    @9
    simpr
    #
    oveq2d
    @35
    cB
    cpnf
    cmnf
    cxad
    @36
    oveq1d
    3eqtr4a
    @4
    cB
    cpnf
    wne
    wa
    @32
    cmnf
    @33
    cB
    xaddmnf2
    cB
    xaddmnf1
    eqtr4d
    pm2.61dane
    adantl
    @31
    cA
    cmnf
    cB
    cxad
    @3
    @4
    simpl
    #
    oveq1d
    @31
    cA
    cmnf
    cB
    cxad
    @37
    oveq2d
    3eqtr4d
    3jaoian
    sylanb
end
