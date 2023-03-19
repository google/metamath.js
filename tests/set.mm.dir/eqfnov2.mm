include "cxp.mm"
include "wfn.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "eqfnov.mm"
include "simpr.mm"
include "eqidd.mm"
include "ancri.mm"
include "impbii.mm"
include "syl6bb.mm"

theorem eqfnov2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  assert |- ( ( F Fn ( A X. B ) /\ G Fn ( A X. B ) ) -> ( F = G <-> A. x e. A A. y e. B ( x F y ) = ( x G y ) ) )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    cG
    @0
    wfn
    wa
    cF
    cG
    wceq
    @0
    @0
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    @2
    @3
    cG
    co
    wceq
    vy
    cB
    wral
    vx
    cA
    wral
    #
    wa
    #
    @4
    vx
    vy
    cA
    cB
    cA
    cB
    cF
    cG
    eqfnov
    @5
    @4
    @1
    @4
    simpr
    @4
    @1
    @4
    @0
    eqidd
    ancri
    impbii
    syl6bb
end
