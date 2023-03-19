include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elxp.mm"
include "vex.mm"
include "pm3.2i.mm"
include "biantru.mm"
include "2exbii.mm"
include "bitr4i.mm"

theorem elvv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( A e. ( _V X. _V ) <-> E. x E. y A = <. x , y >. )

  proof
    cA
    cvv
    cvv
    cxp
    wcel
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    wceq
    #
    @0
    cvv
    wcel
    #
    @1
    cvv
    wcel
    #
    wa
    #
    wa
    #
    vy
    wex
    vx
    wex
    @2
    vy
    wex
    vx
    wex
    vx
    vy
    cA
    cvv
    cvv
    elxp
    @2
    @6
    vx
    vy
    @5
    @2
    @3
    @4
    vx
    vex
    vy
    vex
    pm3.2i
    biantru
    2exbii
    bitr4i
end
