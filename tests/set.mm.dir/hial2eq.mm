include "chil.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cmv.mm"
include "wi.mm"
include "hvsubcl.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "syl.mm"
include "hi2eq.mm"
include "sylibd.mm"
include "oveq1.mm"
include "ralrimivw.mm"
include "impbid1.mm"

theorem hial2eq
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. ~H /\ B e. ~H ) -> ( A. x e. ~H ( A .ih x ) = ( B .ih x ) <-> A = B ) )

  proof
    cA
    chil
    wcel
    cB
    chil
    wcel
    wa
    #
    cA
    vx
    cv
    #
    csp
    co
    #
    cB
    @1
    csp
    co
    #
    wceq
    #
    vx
    chil
    wral
    #
    cA
    cB
    wceq
    #
    @0
    @5
    cA
    cA
    cB
    cmv
    co
    #
    csp
    co
    #
    cB
    @7
    csp
    co
    #
    wceq
    #
    @6
    @0
    @7
    chil
    wcel
    @5
    @10
    wi
    cA
    cB
    hvsubcl
    @4
    @10
    vx
    @7
    chil
    @1
    @7
    wceq
    @2
    @8
    @3
    @9
    @1
    @7
    cA
    csp
    oveq2
    @1
    @7
    cB
    csp
    oveq2
    eqeq12d
    rspcv
    syl
    cA
    cB
    hi2eq
    sylibd
    @6
    @4
    vx
    chil
    cA
    cB
    @1
    csp
    oveq1
    ralrimivw
    impbid1
end
