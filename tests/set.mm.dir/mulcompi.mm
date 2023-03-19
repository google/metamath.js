include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "cmi.mm"
include "co.mm"
include "wceq.mm"
include "comu.mm"
include "com.mm"
include "pinn.mm"
include "nnmcom.mm"
include "syl2an.mm"
include "mulpiord.mm"
include "ancoms.mm"
include "3eqtr4d.mm"
include "dmmulpi.mm"
include "ndmovcom.mm"
include "pm2.61i.mm"

theorem mulcompi
  let cA: class A
  let cB: class B


  assert |- ( A .N B ) = ( B .N A )

  proof
    cA
    cnpi
    wcel
    #
    cB
    cnpi
    wcel
    #
    wa
    #
    cA
    cB
    cmi
    co
    #
    cB
    cA
    cmi
    co
    #
    wceq
    @2
    cA
    cB
    comu
    co
    #
    cB
    cA
    comu
    co
    #
    @3
    @4
    @0
    cA
    com
    wcel
    cB
    com
    wcel
    @5
    @6
    wceq
    @1
    cA
    pinn
    cB
    pinn
    cA
    cB
    nnmcom
    syl2an
    cA
    cB
    mulpiord
    @1
    @0
    @4
    @6
    wceq
    cB
    cA
    mulpiord
    ancoms
    3eqtr4d
    cA
    cB
    cnpi
    cmi
    dmmulpi
    ndmovcom
    pm2.61i
end
