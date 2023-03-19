include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "simpr.mm"
include "simpl.mm"
include "addcomd.mm"
include "wb.mm"
include "addcl.mm"
include "subadd.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem pncan
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A + B ) - B ) = A )

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
    cA
    cB
    caddc
    co
    #
    cB
    cmin
    co
    cA
    wceq
    #
    cB
    cA
    caddc
    co
    @3
    wceq
    #
    @2
    cB
    cA
    @0
    @1
    simpr
    #
    @0
    @1
    simpl
    #
    addcomd
    @2
    @3
    cc
    wcel
    @1
    @0
    @4
    @5
    wb
    cA
    cB
    addcl
    @6
    @7
    @3
    cB
    cA
    subadd
    syl3anc
    mpbird
end
