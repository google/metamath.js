include "cv.mm"
include "wceq.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "cdm.mm"
include "wral.mm"
include "wrel.mm"
include "wa.mm"
include "wbr.mm"
include "wrmo.mm"
include "wal.mm"
include "wmo.mm"
include "inecmo2.mm"
include "alrmomodm.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem inecmo3
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cR: class R

  disjoint R u
  disjoint R v
  disjoint R x
  disjoint u v
  disjoint u x
  disjoint v x
  assert |- ( ( A. u e. dom R A. v e. dom R ( u = v \/ ( [ u ] R i^i [ v ] R ) = (/) ) /\ Rel R ) <-> ( A. x E* u u R x /\ Rel R ) )

  proof
    vu
    cv
    #
    vv
    cv
    #
    wceq
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
    cR
    cdm
    #
    wral
    vu
    @2
    wral
    cR
    wrel
    #
    wa
    @0
    vx
    cv
    cR
    wbr
    #
    vu
    @2
    wrmo
    vx
    wal
    #
    @3
    wa
    @4
    vu
    wmo
    vx
    wal
    #
    @3
    wa
    vx
    vv
    vu
    @2
    cR
    inecmo2
    @3
    @5
    @6
    vx
    vu
    cR
    alrmomodm
    pm5.32ri
    bitri
end
