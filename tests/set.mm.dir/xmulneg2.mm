include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cxne.mm"
include "cxmu.mm"
include "co.mm"
include "wceq.mm"
include "xmulneg1.mm"
include "ancoms.mm"
include "xnegcl.mm"
include "xmulcom.mm"
include "sylan2.mm"
include "xnegeq.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem xmulneg2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* ) -> ( A *e -e B ) = -e ( A *e B ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cB
    cxne
    #
    cA
    cxmu
    co
    #
    cB
    cA
    cxmu
    co
    #
    cxne
    #
    cA
    @3
    cxmu
    co
    #
    cA
    cB
    cxmu
    co
    #
    cxne
    #
    @1
    @0
    @4
    @6
    wceq
    cB
    cA
    xmulneg1
    ancoms
    @1
    @0
    @3
    cxr
    wcel
    @7
    @4
    wceq
    cB
    xnegcl
    cA
    @3
    xmulcom
    sylan2
    @2
    @8
    @5
    wceq
    @9
    @6
    wceq
    cA
    cB
    xmulcom
    @8
    @5
    xnegeq
    syl
    3eqtr4d
end
