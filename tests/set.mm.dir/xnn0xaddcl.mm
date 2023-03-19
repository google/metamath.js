include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "cxnn0.mm"
include "cxad.mm"
include "co.mm"
include "wi.mm"
include "caddc.mm"
include "nn0addcl.mm"
include "nn0xnn0d.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "rexadd.mm"
include "eleq1d.mm"
include "syl2an.mm"
include "mpbird.mm"
include "a1d.mm"
include "wn.mm"
include "wo.mm"
include "ianor.mm"
include "cpnf.mm"
include "wceq.mm"
include "xnn0nnn0pnf.mm"
include "oveq1.mm"
include "cxr.mm"
include "cmnf.mm"
include "wne.mm"
include "xnn0xrnemnf.mm"
include "xaddpnf2.mm"
include "syl.mm"
include "sylan9eq.mm"
include "ex.mm"
include "expcom.mm"
include "impd.mm"
include "oveq2.mm"
include "xaddpnf1.mm"
include "com23.mm"
include "jaoi.mm"
include "imp.mm"
include "pnf0xnn0.mm"
include "syl6eqel.mm"
include "sylbi.mm"
include "pm2.61i.mm"

theorem xnn0xaddcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. NN0* /\ B e. NN0* ) -> ( A +e B ) e. NN0* )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    #
    cA
    cxnn0
    wcel
    #
    cB
    cxnn0
    wcel
    #
    wa
    #
    cA
    cB
    cxad
    co
    #
    cxnn0
    wcel
    #
    wi
    #
    @2
    @7
    @5
    @2
    @7
    cA
    cB
    caddc
    co
    #
    cxnn0
    wcel
    #
    @2
    @9
    cA
    cB
    nn0addcl
    nn0xnn0d
    @0
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @7
    @10
    wb
    @1
    cA
    nn0re
    cB
    nn0re
    @11
    @12
    wa
    @6
    @9
    cxnn0
    cA
    cB
    rexadd
    eleq1d
    syl2an
    mpbird
    a1d
    @2
    wn
    @0
    wn
    #
    @1
    wn
    #
    wo
    #
    @8
    @0
    @1
    ianor
    @15
    @5
    @7
    @15
    @5
    wa
    @6
    cpnf
    cxnn0
    @15
    @5
    @6
    cpnf
    wceq
    #
    @13
    @5
    @16
    wi
    @14
    @13
    @3
    @4
    @16
    @3
    @13
    @4
    @16
    wi
    #
    @3
    @13
    wa
    cA
    cpnf
    wceq
    #
    @17
    cA
    xnn0nnn0pnf
    @18
    @4
    @16
    @18
    @4
    @6
    cpnf
    cB
    cxad
    co
    #
    cpnf
    cA
    cpnf
    cB
    cxad
    oveq1
    @4
    cB
    cxr
    wcel
    cB
    cmnf
    wne
    wa
    @19
    cpnf
    wceq
    cB
    xnn0xrnemnf
    cB
    xaddpnf2
    syl
    sylan9eq
    ex
    syl
    expcom
    impd
    @14
    @3
    @4
    @16
    @14
    @4
    @3
    @16
    @4
    @14
    @3
    @16
    wi
    #
    @4
    @14
    wa
    cB
    cpnf
    wceq
    #
    @20
    cB
    xnn0nnn0pnf
    @21
    @3
    @16
    @21
    @3
    @6
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
    @3
    cA
    cxr
    wcel
    cA
    cmnf
    wne
    wa
    @22
    cpnf
    wceq
    cA
    xnn0xrnemnf
    cA
    xaddpnf1
    syl
    sylan9eq
    ex
    syl
    expcom
    com23
    impd
    jaoi
    imp
    pnf0xnn0
    syl6eqel
    ex
    sylbi
    pm2.61i
end
