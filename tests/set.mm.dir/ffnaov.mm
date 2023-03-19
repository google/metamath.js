include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cafv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "caov.mm"
include "ffnafv.mm"
include "cop.mm"
include "wceq.mm"
include "afveq2.mm"
include "df-aov.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "ralxp.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem ffnaov
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vw: setvar w
  let vk: setvar k

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
  disjoint k x
  assert |- ( F : ( A X. B ) --> C <-> ( F Fn ( A X. B ) /\ A. x e. A A. y e. B (( x F y )) e. C ) )

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
    cafv
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
    caov
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
    ffnafv
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
    cafv
    @8
    @2
    @11
    cF
    afveq2
    @6
    @7
    cF
    df-aov
    syl6eqr
    eleq1d
    ralxp
    anbi2i
    bitri
end
