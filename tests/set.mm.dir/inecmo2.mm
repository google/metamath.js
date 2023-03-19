include "wrel.mm"
include "cv.mm"
include "wceq.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wral.mm"
include "wbr.mm"
include "wrmo.mm"
include "wal.mm"
include "id.mm"
include "inecmo.mm"
include "pm5.32ri.mm"

theorem inecmo2
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cR: class R

  disjoint A u
  disjoint A v
  disjoint A x
  disjoint u v
  disjoint u x
  disjoint v x
  disjoint R u
  disjoint R v
  disjoint R x
  assert |- ( ( A. u e. A A. v e. A ( u = v \/ ( [ u ] R i^i [ v ] R ) = (/) ) /\ Rel R ) <-> ( A. x E* u e. A u R x /\ Rel R ) )

  proof
    cR
    wrel
    vu
    cv
    #
    vv
    cv
    #
    wceq
    #
    @0
    cR
    cec
    @1
    cR
    cec
    cin
    c0
    wceq
    wo
    vv
    cA
    wral
    vu
    cA
    wral
    @0
    vx
    cv
    cR
    wbr
    vu
    cA
    wrmo
    vx
    wal
    vu
    vv
    vx
    cA
    @0
    @1
    cR
    @2
    id
    inecmo
    pm5.32ri
end
