include "ceven.mm"
include "wcel.mm"
include "codd.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "evenz.mm"
include "zcnd.mm"
include "oddz.mm"
include "negsub.mm"
include "syl2an.mm"
include "onego.mm"
include "epoo.mm"
include "sylan2.mm"
include "eqeltrrd.mm"

theorem emoo
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. Even /\ B e. Odd ) -> ( A - B ) e. Odd )

  proof
    cA
    ceven
    wcel
    #
    cB
    codd
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
    codd
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
    oddz
    zcnd
    cA
    cB
    negsub
    syl2an
    @1
    @0
    @2
    codd
    wcel
    @3
    codd
    wcel
    cB
    onego
    cA
    @2
    epoo
    sylan2
    eqeltrrd
end
