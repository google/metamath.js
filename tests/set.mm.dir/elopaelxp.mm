include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "simpl.mm"
include "2eximi.mm"
include "elopab.mm"
include "elvv.mm"
include "3imtr4i.mm"

theorem elopaelxp
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. { <. x , y >. | ps } -> A e. ( _V X. _V ) )

  proof
    cA
    vx
    cv
    vy
    cv
    cop
    wceq
    #
    wps
    wa
    #
    vy
    wex
    vx
    wex
    @0
    vy
    wex
    vx
    wex
    cA
    wps
    vx
    vy
    copab
    wcel
    cA
    cvv
    cvv
    cxp
    wcel
    @1
    @0
    vx
    vy
    @0
    wps
    simpl
    2eximi
    wps
    vx
    vy
    cA
    elopab
    vx
    vy
    cA
    elvv
    3imtr4i
end
