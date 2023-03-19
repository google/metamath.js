include "cneg.mm"
include "wceq.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "df-neg.mm"
include "eqeq1i.mm"
include "eqcom.mm"
include "bitr3i.mm"
include "0cnd.mm"
include "simpr.mm"
include "simpl.mm"
include "subadd2d.mm"
include "syl5rbbr.mm"

theorem addeq0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A + B ) = 0 <-> A = -u B ) )

  proof
    cA
    cB
    cneg
    #
    wceq
    #
    cc0
    cB
    cmin
    co
    #
    cA
    wceq
    #
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
    cc0
    wceq
    @3
    @0
    cA
    wceq
    @1
    @0
    @2
    cA
    cB
    df-neg
    eqeq1i
    @0
    cA
    eqcom
    bitr3i
    @6
    cc0
    cB
    cA
    @6
    0cnd
    @4
    @5
    simpr
    @4
    @5
    simpl
    subadd2d
    syl5rbbr
end
