include "chil.mm"
include "wcel.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "c0v.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "his6.mm"
include "sylibd.mm"
include "wi.mm"
include "oveq2.mm"
include "hi02.mm"
include "sylan9eq.mm"
include "ex.mm"
include "a1i.mm"
include "ralrimdv.mm"
include "impbid.mm"

theorem hial02
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. ~H -> ( A. x e. ~H ( x .ih A ) = 0 <-> A = 0h ) )

  proof
    cA
    chil
    wcel
    #
    vx
    cv
    #
    cA
    csp
    co
    #
    cc0
    wceq
    #
    vx
    chil
    wral
    #
    cA
    c0v
    wceq
    #
    @0
    @4
    cA
    cA
    csp
    co
    #
    cc0
    wceq
    #
    @5
    @3
    @7
    vx
    cA
    chil
    @1
    cA
    wceq
    @2
    @6
    cc0
    @1
    cA
    cA
    csp
    oveq1
    eqeq1d
    rspcv
    cA
    his6
    sylibd
    @0
    @5
    @3
    vx
    chil
    @5
    @1
    chil
    wcel
    #
    @3
    wi
    wi
    @0
    @5
    @8
    @3
    @5
    @8
    @2
    @1
    c0v
    csp
    co
    cc0
    cA
    c0v
    @1
    csp
    oveq2
    @1
    hi02
    sylan9eq
    ex
    a1i
    ralrimdv
    impbid
end
