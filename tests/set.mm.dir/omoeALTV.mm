include "codd.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "ceven.mm"
include "cc.mm"
include "wceq.mm"
include "oddz.mm"
include "zcnd.mm"
include "negsub.mm"
include "syl2an.mm"
include "onego.mm"
include "opoeALTV.mm"
include "sylan2.mm"
include "eqeltrrd.mm"

theorem omoeALTV
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. Odd /\ B e. Odd ) -> ( A - B ) e. Even )

  proof
    cA
    codd
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
    oddz
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
    ceven
    wcel
    cB
    onego
    cA
    @2
    opoeALTV
    sylan2
    eqeltrrd
end
