include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wex.mm"
include "0fin.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "con3i.mm"
include "neq0.mm"
include "sylib.mm"

theorem nfielex
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( -. A e. Fin -> E. x x e. A )

  proof
    cA
    cfn
    wcel
    #
    wn
    cA
    c0
    wceq
    #
    wn
    vx
    cv
    cA
    wcel
    vx
    wex
    @1
    @0
    @1
    @0
    c0
    cfn
    wcel
    0fin
    cA
    c0
    cfn
    eleq1
    mpbiri
    con3i
    vx
    cA
    neq0
    sylib
end
