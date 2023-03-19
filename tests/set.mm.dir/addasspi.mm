include "cnpi.mm"
include "wcel.mm"
include "w3a.mm"
include "cpli.mm"
include "co.mm"
include "wceq.mm"
include "coa.mm"
include "com.mm"
include "pinn.mm"
include "nnaass.mm"
include "syl3an.mm"
include "wa.mm"
include "addclpi.mm"
include "addpiord.mm"
include "sylan.mm"
include "oveq1d.mm"
include "adantr.mm"
include "eqtrd.mm"
include "3impa.mm"
include "sylan2.mm"
include "oveq2d.mm"
include "adantl.mm"
include "3impb.mm"
include "3eqtr4d.mm"
include "dmaddpi.mm"
include "0npi.mm"
include "ndmovass.mm"
include "pm2.61i.mm"

theorem addasspi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A +N B ) +N C ) = ( A +N ( B +N C ) )

  proof
    cA
    cnpi
    wcel
    #
    cB
    cnpi
    wcel
    #
    cC
    cnpi
    wcel
    #
    w3a
    #
    cA
    cB
    cpli
    co
    #
    cC
    cpli
    co
    #
    cA
    cB
    cC
    cpli
    co
    #
    cpli
    co
    #
    wceq
    @3
    cA
    cB
    coa
    co
    #
    cC
    coa
    co
    #
    cA
    cB
    cC
    coa
    co
    #
    coa
    co
    #
    @5
    @7
    @0
    cA
    com
    wcel
    @1
    cB
    com
    wcel
    @2
    cC
    com
    wcel
    @9
    @11
    wceq
    cA
    pinn
    cB
    pinn
    cC
    pinn
    cA
    cB
    cC
    nnaass
    syl3an
    @0
    @1
    @2
    @5
    @9
    wceq
    @0
    @1
    wa
    #
    @2
    wa
    @5
    @4
    cC
    coa
    co
    #
    @9
    @12
    @4
    cnpi
    wcel
    @2
    @5
    @13
    wceq
    cA
    cB
    addclpi
    @4
    cC
    addpiord
    sylan
    @12
    @13
    @9
    wceq
    @2
    @12
    @4
    @8
    cC
    coa
    cA
    cB
    addpiord
    oveq1d
    adantr
    eqtrd
    3impa
    @0
    @1
    @2
    @7
    @11
    wceq
    @0
    @1
    @2
    wa
    #
    wa
    @7
    cA
    @6
    coa
    co
    #
    @11
    @14
    @0
    @6
    cnpi
    wcel
    @7
    @15
    wceq
    cB
    cC
    addclpi
    cA
    @6
    addpiord
    sylan2
    @14
    @15
    @11
    wceq
    @0
    @14
    @6
    @10
    cA
    coa
    cB
    cC
    addpiord
    oveq2d
    adantl
    eqtrd
    3impb
    3eqtr4d
    cA
    cB
    cC
    cnpi
    cpli
    dmaddpi
    0npi
    ndmovass
    pm2.61i
end
