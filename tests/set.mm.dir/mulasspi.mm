include "cnpi.mm"
include "wcel.mm"
include "w3a.mm"
include "cmi.mm"
include "co.mm"
include "wceq.mm"
include "comu.mm"
include "com.mm"
include "pinn.mm"
include "nnmass.mm"
include "syl3an.mm"
include "wa.mm"
include "mulclpi.mm"
include "mulpiord.mm"
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
include "dmmulpi.mm"
include "0npi.mm"
include "ndmovass.mm"
include "pm2.61i.mm"

theorem mulasspi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A .N B ) .N C ) = ( A .N ( B .N C ) )

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
    cmi
    co
    #
    cC
    cmi
    co
    #
    cA
    cB
    cC
    cmi
    co
    #
    cmi
    co
    #
    wceq
    @3
    cA
    cB
    comu
    co
    #
    cC
    comu
    co
    #
    cA
    cB
    cC
    comu
    co
    #
    comu
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
    nnmass
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
    comu
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
    mulclpi
    @4
    cC
    mulpiord
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
    comu
    cA
    cB
    mulpiord
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
    comu
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
    mulclpi
    cA
    @6
    mulpiord
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
    comu
    cB
    cC
    mulpiord
    oveq2d
    adantl
    eqtrd
    3impb
    3eqtr4d
    cA
    cB
    cC
    cnpi
    cmi
    dmmulpi
    0npi
    ndmovass
    pm2.61i
end
