include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cmv.mm"
include "wi.mm"
include "csh.mm"
include "spansnsh.mm"
include "adantr.mm"
include "simpr.mm"
include "spansnid.mm"
include "shsubcl.mm"
include "syl3anc.mm"
include "ex.mm"
include "hvpncan2.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "shaddcl.mm"
include "3expia.mm"
include "syl2anc.mm"
include "impbid.mm"

theorem sumspansn
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( ( A +h B ) e. ( span ` { A } ) <-> B e. ( span ` { A } ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    #
    cA
    cB
    cva
    co
    #
    cA
    csn
    cspn
    cfv
    #
    wcel
    #
    cB
    @4
    wcel
    #
    @2
    @5
    @3
    cA
    cmv
    co
    #
    @4
    wcel
    #
    @6
    @0
    @5
    @8
    wi
    @1
    @0
    @5
    @8
    @0
    @5
    wa
    @4
    csh
    wcel
    #
    @5
    cA
    @4
    wcel
    #
    @8
    @0
    @9
    @5
    cA
    spansnsh
    #
    adantr
    @0
    @5
    simpr
    @0
    @10
    @5
    cA
    spansnid
    #
    adantr
    @3
    cA
    @4
    shsubcl
    syl3anc
    ex
    adantr
    @2
    @7
    cB
    @4
    cA
    cB
    hvpncan2
    eleq1d
    sylibd
    @0
    @6
    @5
    wi
    #
    @1
    @0
    @9
    @10
    @13
    @11
    @12
    @9
    @10
    @6
    @5
    cA
    cB
    @4
    shaddcl
    3expia
    syl2anc
    adantr
    impbid
end
