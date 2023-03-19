include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cph.mm"
include "co.mm"
include "chj.mm"
include "spansnj.mm"
include "spansnch.mm"
include "chjcl.mm"
include "sylan2.mm"
include "eqeltrd.mm"

theorem spansnscl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. ~H ) -> ( A +H ( span ` { B } ) ) e. CH )

  proof
    cA
    cch
    wcel
    #
    cB
    chil
    wcel
    #
    wa
    cA
    cB
    csn
    cspn
    cfv
    #
    cph
    co
    cA
    @2
    chj
    co
    #
    cch
    cA
    cB
    spansnj
    @1
    @0
    @2
    cch
    wcel
    @3
    cch
    wcel
    cB
    spansnch
    cA
    @2
    chjcl
    sylan2
    eqeltrd
end
