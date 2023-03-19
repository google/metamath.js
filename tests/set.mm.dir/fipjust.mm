include "cv.mm"
include "cin.mm"
include "wcel.mm"
include "weq.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "ineq2.mm"
include "cbvral2v.mm"

theorem fipjust
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A

  disjoint u v
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A. u e. A A. v e. A ( u i^i v ) e. A <-> A. x e. A A. y e. A ( x i^i y ) e. A )

  proof
    vu
    cv
    #
    vv
    cv
    #
    cin
    #
    cA
    wcel
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    cA
    wcel
    @3
    @1
    cin
    #
    cA
    wcel
    vu
    vv
    vx
    vy
    cA
    cA
    vu
    vx
    weq
    @2
    @6
    cA
    @0
    @3
    @1
    ineq1
    eleq1d
    vv
    vy
    weq
    @6
    @5
    cA
    @1
    @4
    @3
    ineq2
    eleq1d
    cbvral2v
end
