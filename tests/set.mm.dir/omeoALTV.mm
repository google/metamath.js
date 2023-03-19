include "codd.mm"
include "wcel.mm"
include "ceven.mm"
include "wa.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "oddz.mm"
include "zcnd.mm"
include "evenz.mm"
include "negsub.mm"
include "syl2an.mm"
include "enege.mm"
include "opeoALTV.mm"
include "sylan2.mm"
include "eqeltrrd.mm"

theorem omeoALTV
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. Odd /\ B e. Even ) -> ( A - B ) e. Odd )

  proof
    cA
    codd
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
    oddz
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
    codd
    wcel
    cB
    enege
    cA
    @2
    opeoALTV
    sylan2
    eqeltrrd
end
