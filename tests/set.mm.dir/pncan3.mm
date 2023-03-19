include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "caddc.mm"
include "eqid.mm"
include "wb.mm"
include "simpr.mm"
include "simpl.mm"
include "subcl.mm"
include "ancoms.mm"
include "subadd.mm"
include "syl3anc.mm"
include "mpbii.mm"

theorem pncan3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( A + ( B - A ) ) = B )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cB
    cA
    cmin
    co
    #
    @3
    wceq
    #
    cA
    @3
    caddc
    co
    cB
    wceq
    #
    @3
    eqid
    @2
    @1
    @0
    @3
    cc
    wcel
    #
    @4
    @5
    wb
    @0
    @1
    simpr
    @0
    @1
    simpl
    @1
    @0
    @6
    cB
    cA
    subcl
    ancoms
    cB
    cA
    @3
    subadd
    syl3anc
    mpbii
end
