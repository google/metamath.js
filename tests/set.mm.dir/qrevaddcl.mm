include "cq.mm"
include "wcel.mm"
include "cc.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "cmin.mm"
include "wceq.mm"
include "qcn.mm"
include "pncan.mm"
include "sylan2.mm"
include "ancoms.mm"
include "adantr.mm"
include "qsubcl.mm"
include "adantlr.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "wi.mm"
include "qaddcl.mm"
include "expcom.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "pm4.71ri.mm"
include "syl6bbr.mm"

theorem qrevaddcl
  let cA: class A
  let cB: class B


  assert |- ( B e. QQ -> ( ( A e. CC /\ ( A + B ) e. QQ ) <-> A e. QQ ) )

  proof
    cB
    cq
    wcel
    #
    cA
    cc
    wcel
    #
    cA
    cB
    caddc
    co
    #
    cq
    wcel
    #
    wa
    @1
    cA
    cq
    wcel
    #
    wa
    @4
    @0
    @1
    @3
    @4
    @0
    @1
    wa
    #
    @3
    @4
    @5
    @3
    @4
    @5
    @3
    wa
    @2
    cB
    cmin
    co
    #
    cA
    cq
    @5
    @6
    cA
    wceq
    #
    @3
    @1
    @0
    @7
    @0
    @1
    cB
    cc
    wcel
    @7
    cB
    qcn
    cA
    cB
    pncan
    sylan2
    ancoms
    adantr
    @0
    @3
    @6
    cq
    wcel
    #
    @1
    @3
    @0
    @8
    @2
    cB
    qsubcl
    ancoms
    adantlr
    eqeltrrd
    ex
    @0
    @4
    @3
    wi
    @1
    @4
    @0
    @3
    cA
    cB
    qaddcl
    expcom
    adantr
    impbid
    pm5.32da
    @4
    @1
    cA
    qcn
    pm4.71ri
    syl6bbr
end
