include "cz.mm"
include "wcel.mm"
include "ceven.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wi.mm"
include "epee.mm"
include "expcom.mm"
include "adantl.mm"
include "cmin.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "evenz.mm"
include "zcnd.mm"
include "pncan.mm"
include "syl2an.mm"
include "adantr.mm"
include "simpr.mm"
include "anim1i.mm"
include "ancomd.mm"
include "emee.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "impbid.mm"

theorem evensumeven
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. ZZ /\ B e. Even ) -> ( A e. Even <-> ( A + B ) e. Even ) )

  proof
    cA
    cz
    wcel
    #
    cB
    ceven
    wcel
    #
    wa
    #
    cA
    ceven
    wcel
    #
    cA
    cB
    caddc
    co
    #
    ceven
    wcel
    #
    @1
    @3
    @5
    wi
    @0
    @3
    @1
    @5
    cA
    cB
    epee
    expcom
    adantl
    @2
    @5
    @3
    @2
    @5
    wa
    #
    @4
    cB
    cmin
    co
    #
    cA
    ceven
    @2
    @7
    cA
    wceq
    #
    @5
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @8
    @1
    cA
    zcn
    @1
    cB
    cB
    evenz
    zcnd
    cA
    cB
    pncan
    syl2an
    adantr
    @6
    @5
    @1
    wa
    @7
    ceven
    wcel
    @6
    @1
    @5
    @2
    @1
    @5
    @0
    @1
    simpr
    anim1i
    ancomd
    @4
    cB
    emee
    syl
    eqeltrrd
    ex
    impbid
end
