include "cnpi.mm"
include "wcel.mm"
include "wa.mm"
include "cpli.mm"
include "co.mm"
include "wceq.mm"
include "coa.mm"
include "com.mm"
include "pinn.mm"
include "nnacom.mm"
include "syl2an.mm"
include "addpiord.mm"
include "ancoms.mm"
include "3eqtr4d.mm"
include "dmaddpi.mm"
include "ndmovcom.mm"
include "pm2.61i.mm"

theorem addcompi
  let cA: class A
  let cB: class B


  assert |- ( A +N B ) = ( B +N A )

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
    cpli
    co
    #
    cB
    cA
    cpli
    co
    #
    wceq
    @2
    cA
    cB
    coa
    co
    #
    cB
    cA
    coa
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
    nnacom
    syl2an
    cA
    cB
    addpiord
    @1
    @0
    @4
    @6
    wceq
    cB
    cA
    addpiord
    ancoms
    3eqtr4d
    cA
    cB
    cnpi
    cpli
    dmaddpi
    ndmovcom
    pm2.61i
end
