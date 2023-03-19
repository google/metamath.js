include "wrel.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cxp.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "wss.mm"
include "df-rel.mm"
include "biimpi.mm"
include "sselda.mm"
include "elvv.mm"
include "sylib.mm"

theorem elrel
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( ( Rel R /\ A e. R ) -> E. x E. y A = <. x , y >. )

  proof
    cR
    wrel
    #
    cA
    cR
    wcel
    wa
    cA
    cvv
    cvv
    cxp
    #
    wcel
    cA
    vx
    cv
    vy
    cv
    cop
    wceq
    vy
    wex
    vx
    wex
    @0
    cR
    @1
    cA
    @0
    cR
    @1
    wss
    cR
    df-rel
    biimpi
    sselda
    vx
    vy
    cA
    elvv
    sylib
end
