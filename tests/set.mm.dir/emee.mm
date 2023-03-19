include "ceven.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "evenz.mm"
include "zcnd.mm"
include "negsub.mm"
include "syl2an.mm"
include "enege.mm"
include "epee.mm"
include "sylan2.mm"
include "eqeltrrd.mm"

theorem emee
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. Even /\ B e. Even ) -> ( A - B ) e. Even )

  proof
    cA
    ceven
    wcel
    #
    cB
    ceven
    wcel
    #
    wa
    cA
    cB
    cneg
    #
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    ceven
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @3
    @4
    wceq
    @1
    @0
    cA
    cA
    evenz
    zcnd
    @1
    cB
    cB
    evenz
    zcnd
    cA
    cB
    negsub
    syl2an
    @1
    @0
    @2
    ceven
    wcel
    @3
    ceven
    wcel
    cB
    enege
    cA
    @2
    epee
    sylan2
    eqeltrrd
end
