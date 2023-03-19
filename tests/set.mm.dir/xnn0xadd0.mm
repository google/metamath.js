include "cxnn0.mm"
include "wcel.mm"
include "wa.mm"
include "cxad.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "cpnf.mm"
include "wo.mm"
include "elxnn0.mm"
include "caddc.mm"
include "cr.mm"
include "nn0re.mm"
include "rexadd.mm"
include "syl2an.mm"
include "eqeq1d.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "nn0ge0.mm"
include "jca.mm"
include "add20.mm"
include "bitrd.mm"
include "biimpd.mm"
include "expcom.mm"
include "oveq2.mm"
include "adantr.mm"
include "cxr.mm"
include "cmnf.mm"
include "wne.mm"
include "nn0xnn0.mm"
include "xnn0xrnemnf.mm"
include "xaddpnf1.mm"
include "3syl.mm"
include "adantl.mm"
include "0re.mm"
include "renepnf.mm"
include "ax-mp.mm"
include "nesymi.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "ex.mm"
include "jaoi.mm"
include "sylbi.mm"
include "com12.mm"
include "oveq1.mm"
include "xaddpnf2.mm"
include "syl.mm"
include "sylan9bb.mm"
include "imp.mm"
include "oveq12.mm"
include "0xr.mm"
include "xaddid1.mm"
include "syl6eq.mm"
include "impbid1.mm"

theorem xnn0xadd0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN0* /\ B e. NN0* ) -> ( ( A +e B ) = 0 <-> ( A = 0 /\ B = 0 ) ) )

  proof
    cA
    cxnn0
    wcel
    #
    cB
    cxnn0
    wcel
    #
    wa
    cA
    cB
    cxad
    co
    #
    cc0
    wceq
    #
    cA
    cc0
    wceq
    cB
    cc0
    wceq
    wa
    #
    @0
    @1
    @3
    @4
    wi
    #
    @0
    cA
    cn0
    wcel
    #
    cA
    cpnf
    wceq
    #
    wo
    @1
    @5
    wi
    #
    cA
    elxnn0
    @6
    @8
    @7
    @1
    @6
    @5
    @1
    cB
    cn0
    wcel
    #
    cB
    cpnf
    wceq
    #
    wo
    @6
    @5
    wi
    #
    cB
    elxnn0
    @9
    @11
    @10
    @6
    @9
    @5
    @6
    @9
    wa
    #
    @3
    @4
    @12
    @3
    cA
    cB
    caddc
    co
    #
    cc0
    wceq
    #
    @4
    @12
    @2
    @13
    cc0
    @6
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @2
    @13
    wceq
    @9
    cA
    nn0re
    #
    cB
    nn0re
    #
    cA
    cB
    rexadd
    syl2an
    eqeq1d
    @6
    @15
    cc0
    cA
    cle
    wbr
    #
    wa
    @16
    cc0
    cB
    cle
    wbr
    #
    wa
    @14
    @4
    wb
    @9
    @6
    @15
    @19
    @17
    cA
    nn0ge0
    jca
    @9
    @16
    @20
    @18
    cB
    nn0ge0
    jca
    cA
    cB
    add20
    syl2an
    bitrd
    biimpd
    expcom
    @10
    @6
    @5
    @10
    @6
    wa
    #
    @3
    cpnf
    cc0
    wceq
    #
    @4
    @21
    @3
    cA
    cpnf
    cxad
    co
    #
    cc0
    wceq
    #
    @22
    @10
    @3
    @24
    wb
    @6
    @10
    @2
    @23
    cc0
    cB
    cpnf
    cA
    cxad
    oveq2
    eqeq1d
    adantr
    @21
    @23
    cpnf
    cc0
    @6
    @23
    cpnf
    wceq
    #
    @10
    @6
    @0
    cA
    cxr
    wcel
    cA
    cmnf
    wne
    wa
    @25
    cA
    nn0xnn0
    cA
    xnn0xrnemnf
    cA
    xaddpnf1
    3syl
    adantl
    eqeq1d
    bitrd
    @22
    @4
    cc0
    cpnf
    cc0
    cr
    wcel
    cc0
    cpnf
    wne
    0re
    cc0
    renepnf
    ax-mp
    nesymi
    pm2.21i
    #
    syl6bi
    ex
    jaoi
    sylbi
    com12
    @7
    @1
    @5
    @7
    @1
    wa
    @3
    @22
    @4
    @7
    @3
    cpnf
    cB
    cxad
    co
    #
    cc0
    wceq
    @1
    @22
    @7
    @2
    @27
    cc0
    cA
    cpnf
    cB
    cxad
    oveq1
    eqeq1d
    @1
    @27
    cpnf
    cc0
    @1
    cB
    cxr
    wcel
    cB
    cmnf
    wne
    wa
    @27
    cpnf
    wceq
    cB
    xnn0xrnemnf
    cB
    xaddpnf2
    syl
    eqeq1d
    sylan9bb
    @26
    syl6bi
    ex
    jaoi
    sylbi
    imp
    @4
    @2
    cc0
    cc0
    cxad
    co
    #
    cc0
    cA
    cc0
    cB
    cc0
    cxad
    oveq12
    cc0
    cxr
    wcel
    @28
    cc0
    wceq
    0xr
    cc0
    xaddid1
    ax-mp
    syl6eq
    impbid1
end
