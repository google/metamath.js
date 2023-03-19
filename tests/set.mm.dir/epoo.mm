include "ceven.mm"
include "wcel.mm"
include "codd.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cc.mm"
include "wceq.mm"
include "evenz.mm"
include "zcnd.mm"
include "oddz.mm"
include "addcom.mm"
include "syl2an.mm"
include "opeoALTV.mm"
include "ancoms.mm"
include "eqeltrd.mm"

theorem epoo
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. Even /\ B e. Odd ) -> ( A + B ) e. Odd )

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
    caddc
    co
    #
    cB
    cA
    caddc
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
    @2
    @3
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
    addcom
    syl2an
    @1
    @0
    @3
    codd
    wcel
    cB
    cA
    opeoALTV
    ancoms
    eqeltrd
end
