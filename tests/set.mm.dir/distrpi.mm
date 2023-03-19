include "cnpi.mm"
include "wcel.mm"
include "w3a.mm"
include "cpli.mm"
include "co.mm"
include "cmi.mm"
include "wceq.mm"
include "coa.mm"
include "comu.mm"
include "com.mm"
include "pinn.mm"
include "nndi.mm"
include "syl3an.mm"
include "wa.mm"
include "addclpi.mm"
include "mulpiord.mm"
include "sylan2.mm"
include "addpiord.mm"
include "oveq2d.mm"
include "adantl.mm"
include "eqtrd.mm"
include "3impb.mm"
include "mulclpi.mm"
include "syl2an.mm"
include "oveqan12d.mm"
include "3impdi.mm"
include "3eqtr4d.mm"
include "dmaddpi.mm"
include "0npi.mm"
include "dmmulpi.mm"
include "ndmovdistr.mm"
include "pm2.61i.mm"

theorem distrpi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A .N ( B +N C ) ) = ( ( A .N B ) +N ( A .N C ) )

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
    cC
    cpli
    co
    #
    cmi
    co
    #
    cA
    cB
    cmi
    co
    #
    cA
    cC
    cmi
    co
    #
    cpli
    co
    #
    wceq
    @3
    cA
    cB
    cC
    coa
    co
    #
    comu
    co
    #
    cA
    cB
    comu
    co
    #
    cA
    cC
    comu
    co
    #
    coa
    co
    #
    @5
    @8
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
    @10
    @13
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
    nndi
    syl3an
    @0
    @1
    @2
    @5
    @10
    wceq
    @0
    @1
    @2
    wa
    #
    wa
    @5
    cA
    @4
    comu
    co
    #
    @10
    @14
    @0
    @4
    cnpi
    wcel
    @5
    @15
    wceq
    cB
    cC
    addclpi
    cA
    @4
    mulpiord
    sylan2
    @14
    @15
    @10
    wceq
    @0
    @14
    @4
    @9
    cA
    comu
    cB
    cC
    addpiord
    oveq2d
    adantl
    eqtrd
    3impb
    @0
    @1
    @2
    @8
    @13
    wceq
    @0
    @1
    wa
    #
    @0
    @2
    wa
    #
    wa
    @8
    @6
    @7
    coa
    co
    #
    @13
    @16
    @6
    cnpi
    wcel
    @7
    cnpi
    wcel
    @8
    @18
    wceq
    @17
    cA
    cB
    mulclpi
    cA
    cC
    mulclpi
    @6
    @7
    addpiord
    syl2an
    @16
    @17
    @6
    @11
    @7
    @12
    coa
    cA
    cB
    mulpiord
    cA
    cC
    mulpiord
    oveqan12d
    eqtrd
    3impdi
    3eqtr4d
    cA
    cB
    cC
    cnpi
    cpli
    cmi
    dmaddpi
    0npi
    dmmulpi
    ndmovdistr
    pm2.61i
end
