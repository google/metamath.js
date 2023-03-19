include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "co.mm"
include "ffnfv.mm"
include "cop.mm"
include "wceq.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "ralxp.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem ffnov
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vw: setvar w

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint F x
  disjoint F y
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint B w
  disjoint C w
  disjoint F w
  assert |- ( F : ( A X. B ) --> C <-> ( F Fn ( A X. B ) /\ A. x e. A A. y e. B ( x F y ) e. C ) )

  proof
    cA
    cB
    cxp
    #
    cC
    cF
    wf
    cF
    @0
    wfn
    #
    vw
    cv
    #
    cF
    cfv
    #
    cC
    wcel
    #
    vw
    @0
    wral
    #
    wa
    @1
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    cC
    wcel
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    wa
    vw
    @0
    cC
    cF
    ffnfv
    @5
    @10
    @1
    @4
    @9
    vw
    vx
    vy
    cA
    cB
    @2
    @6
    @7
    cop
    #
    wceq
    #
    @3
    @8
    cC
    @12
    @3
    @11
    cF
    cfv
    @8
    @2
    @11
    cF
    fveq2
    @6
    @7
    cF
    df-ov
    syl6eqr
    eleq1d
    ralxp
    anbi2i
    bitri
end
